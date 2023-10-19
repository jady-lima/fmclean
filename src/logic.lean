
section propositional

variables P Q R : Prop

------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  := by
  intro p
  intro notp
  have f: False := notp p
  exact f

theorem doubleneg_elim :
  ¬¬P → P  := by
  intro notp
  by_cases p: P
  exact p
  apply False.elim (notp p)

theorem doubleneg_law :
  ¬¬P ↔ P  := by
  apply Iff.intro
  apply doubleneg_elim 
  apply doubleneg_intro 

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
    intro hpq
    apply Or.elim hpq
    apply Or.intro_right
    apply Or.intro_left

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro hpq
  apply And.intro
  apply And.right hpq
  apply And.left hpq

------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  := by
  intro h
  intro p
  apply Or.elim h
  intro notp
  apply False.elim (notp p)
  intro q
  exact q

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  := by
  intro hpq
  intro notp
  apply Or.elim hpq
  intro p 
  apply False.elim (notp p)
  intro q
  exact q

------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  := by
  intro hpq
  intro notq
  intro p
  have q:Q := hpq p 
  exact False.elim (notq q)

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  := by
  intro h
  intro p 
  by_cases q:Q
  exact q
  have notp: ¬P := h q
  exact False.elim (notp p)

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  := by
  apply Iff.intro
  apply impl_as_contrapositive
  apply impl_as_contrapositive_converse

------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  := by
  intro npnotp
  suffices pnotp: (P∨¬P) from npnotp pnotp
  apply Or.inr
  intro p
  suffices pnotp: (P∨¬P) from npnotp pnotp
  apply Or.inl
  exact p

------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  := by
  intro hpqp
  intro notp
  suffices notnotp: (P → Q) from notp (hpqp notnotp)
  intro p
  apply False.elim (notp p)

------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  := by
  intro hpq
  intro nnpnq
  apply Or.elim hpq
  intro p
  apply And.left nnpnq p
  intro q 
  apply And.right nnpnq q

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  := by
  intro hpq
  intro npnq
  apply Or.elim npnq 
  intro np
  apply np 
  exact And.left hpq
  intro nq 
  apply nq
  exact And.right hpq

------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  := by 
  intro npq
  apply And.intro
  intro p
  suffices pq: (P∨Q) from npq pq
  exact Or.inl p
  intro q
  suffices pq: (P∨Q) from npq pq
  exact Or.inr q

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  := by
  intro npnq
  intro notpq
  



theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  sorry,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  sorry,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  sorry,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  sorry,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  sorry,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  sorry,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  sorry,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  sorry,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  sorry,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  sorry,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  sorry,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  sorry,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  sorry,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  sorry,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  sorry,
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
  sorry,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
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
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
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
