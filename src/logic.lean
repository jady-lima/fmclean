
section propositional

variables P Q R : Prop

------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  := by
  begin
    intro p,
    intro notp,
    apply notp,
    exact p,
  end

theorem doubleneg_elim :
  ¬¬P → P  := by
  begin
    intro notp,
    by_cases p : P,
      exact p,
      apply false.elim (notp p),
  end

theorem doubleneg_law :
  ¬¬P ↔ P  := by
  begin
    split,
      apply doubleneg_elim,
      apply doubleneg_intro,
  end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  begin
    intro pq,
    cases pq with p q,
      right,
      exact p,
      left,
      exact q,
  end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  begin
    intro pq,
    split,
      cases pq with left right,
        exact right,
      cases pq with left right,
        exact left,
  end

------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  := by
  begin
    intro npq,
    intro p,
    apply or.elim npq,
    intro np,
    apply false.elim (np p),
    intro q,
    exact q,
  end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  := by
  begin
    intro pq,
    intro np,
    apply or.elim pq,
    intro p,
    apply false.elim (np p),
    intro q,
    apply q,
  end

------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  := by
  begin
    intro pq,
    intro nq,
    intro p,
    have q : Q := pq p,
    apply nq,
    exact q,
  end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  := by
  begin
    intro npnq,
    intro p,
    by_cases q:Q,
      exact q,
      have np : ¬P := npnq q,
      exact false.elim (np p),
  end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  := by
  begin
    split,
      apply impl_as_contrapositive,
      apply impl_as_contrapositive_converse,
  end

------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  := by
  begin
    intro nnpnp,
    apply nnpnp,
    by_cases p:P,
      left,
      exact p,
      right,
      exact p,   
  end

------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  := by
  begin
    intro pqp,
    intro np, 
    by_cases p:P,
      apply np,
      exact p,
      apply np,
      apply pqp,
      intro p,
      exfalso,
      apply np,
      exact p,
  end

------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  := by
  begin
    intro pq,
    intro npnq,
    apply or.elim pq,
    intro p,
    apply and.left npnq,
    exact p,
    intro q,
    apply and.right npnq,
    exact q,
  end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  := by
  begin
    intro pq,
    intro npnq,
    cases npnq with np nq,
      apply np,
      exact and.left pq,
      apply nq,
      exact and.right pq,
  end

------------------------------------------------
-- As leis de De Morgan para ∨,∧:'
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  := by 
  begin
    intro npq,
    split,
      intro p,
      apply npq,
      left,
      exact p,
      intro q,
      apply npq,
      right,
      exact q,
  end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  := by
  begin
    intro npnq,
    intro pq,
    cases pq with p q,
      apply and.left npnq,
      exact p,
      apply and.right npnq,
      exact q,
  end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
  begin
    intro npq,
    exfalso,
    apply npq,
    split,
      
  end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
  begin
    intro nqnp,
    intro pq,
    cases nqnp with nq np,
      apply nq,
      exact and.right pq,
      apply np,
      exact and.left pq,
  end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
  begin
    split,
      apply demorgan_conj,
      apply demorgan_conj_converse,
  end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
  begin
    split,
      apply demorgan_disj,
      apply demorgan_disj_converse,
  end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
  begin
    intro pqr,
    cases pqr with p qr,
      cases qr with q r,
        left,
        split,
          exact p,
          exact q,
        right,
        split,
          exact p,
          exact r,
  end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
  begin
    intro pqpr,
    cases pqpr with pq pr,
      split,
        exact and.left pq,
        left,
        exact and.right pq,
      split,
        exact and.left pr,
        right,
        exact and.right pr,
  end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
  begin
    intro pqr,
    cases pqr with p qr,
      split,
        left,
        exact p,
        left,
        exact p,
      cases qr with q r,
        split,
          right,
          exact q,
          right,
          exact r,
  end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
  begin
    intro pqpr,
    cases pqpr with pq pr,
      cases pq with p q,
        left,
        exact p,
        right,
        split,
          exact q,         

  end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
  begin
    intro pqr,
    intro p,
    intro q,
    apply pqr,
    split,
      exact p,
      exact q,
  end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
  begin
    intro pqr,
    intro pq,
    apply pqr,
    exact and.left pq,
    exact and.right pq,
  end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
  begin
    intro p,
    exact p,
  end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
  begin
    intro p,
    left,
    exact p,
  end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
  begin
    intro q,
    right,
    exact q,
  end

theorem weaken_conj_right :
  (P∧Q) → P  :=
  begin
    intro pq,
    exact and.left pq,
  end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
  begin
    intro pq,
    exact and.right pq,
  end

theorem conj_idempot :
  (P∧P) ↔ P :=
  begin
    split,
      apply weaken_conj_left,
      intro p,
      split,
        exact p,
        exact p,
  end

theorem disj_idempot :
  (P∨P) ↔ P  :=
  begin
    split,
      intro pp,
      cases pp with p p,
        exact p,
        exact p,
      intro p,
      right,
      exact p,
  end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
  begin
    intro npx,
    intro u,
    intro pu,
    apply npx,
    existsi u,
    exact pu,
  end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
  begin
    intro anpx,
    intro enpx,
    apply exists.elim enpx,
    intro u,
    intro pu,
    have npu : ¬P u := anpx u,
    apply npu,
    exact pu,      
  end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
  begin
    intro napx,
    apply classical.by_contradiction,
    intro nenpx,
    apply napx,
    intro u,
    have pu : P u := exists.elim napx u,
  end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
  begin
    intro enpx,
    intro napx,
    
  end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
  begin
    split,
      apply demorgan_forall,
      apply demorgan_forall_converse,
  end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
  begin
    split,
      apply demorgan_exists,
      apply demorgan_exists_converse,
  end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
  begin
    intro epx,
    intro nanpx,
    cases epx with u pu,
    
  end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
  begin
    intro apx,
    intro nenpx,
    cases nenpx with u npu,
      
  end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
  begin
    intro nenpx,
    intro apx,
  end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
  begin
    split,
      apply forall_as_neg_exists,
      apply forall_as_neg_exists_converse,
  end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
  begin
    split,
      apply exists_as_neg_forall,
      apply exists_as_neg_forall_converse,
  end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
  begin
    intro pxqx,
    intro pxepq,
    split,

  end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
  begin
    intro apxapq,
    intro pxqx,
    cases apxapq with px qx,
      
      
  end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
