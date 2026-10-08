-- Prove2me | solution 1 for SemialgebraicSDP.Psatz.cone_empty_eq_isSumSq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:48:52.018911+00:00
-- url     : https://prove2.me/submissions/894b28fa-6d0d-412c-ad1f-eacec1aea891

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Cone

open SemialgebraicSDP.Psatz MvPolynomial

theorem solution (n : ℕ) :
    cone (∅ : Set (MvPolynomial (Fin n) ℝ)) = {a | IsSumSq a} ∧
      ∀ P : Set (MvPolynomial (Fin n) ℝ),
        (∀ a ∈ P, ∀ b ∈ P, a + b ∈ P) → (∀ a ∈ P, ∀ b ∈ P, a * b ∈ P) →
        (∀ a : MvPolynomial (Fin n) ℝ, a ^ 2 ∈ P) → cone ∅ ⊆ P := by
  constructor
  · ext a
    constructor
    · intro ha
      change InCone ∅ a at ha
      induction ha with
      | of_mem h => exact False.elim h
      | sq a => simpa [pow_two] using IsSumSq.mul_self a
      | add ha hb iha ihb => exact iha.add ihb
      | mul ha hb iha ihb => exact iha.mul ihb
    · intro ha
      induction ha with
      | zero => simpa [cone] using InCone.sq (S := ∅) 0
      | sq_add a h ih =>
        exact InCone.add (by simpa [pow_two] using InCone.sq (S := ∅) a) ih
  · intro P hadd hmul hsq a ha
    change InCone ∅ a at ha
    induction ha with
    | of_mem h => exact False.elim h
    | sq a => exact hsq a
    | add ha hb iha ihb => exact hadd _ iha _ ihb
    | mul ha hb iha ihb => exact hmul _ iha _ ihb

#print axioms solution
