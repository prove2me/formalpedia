-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P38.correction_dependency
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T08:34:51.671205+00:00
-- url     : https://prove2.me/submissions/da9e53c5-eba1-4a6b-8e69-f722f4b17869

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Intakenext100.P38 in
theorem solution {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    correctionC n k = ((k : ℝ) - 2) • correctionA n k - correctionB n k ∧
    ¬ LinearIndependent ℝ (![correctionA n k, correctionB n k, correctionC n k] :
      Fin 3 → QnnOperator n) := by
  have h1 : correctionC n k = ((k : ℝ) - 2) • correctionA n k - correctionB n k := by
    unfold correctionA correctionB correctionC
    module
  refine ⟨h1, fun hli => ?_⟩
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli ![(k : ℝ) - 2, -1, -1] (by
    simp only [Fin.sum_univ_three, Matrix.cons_val]
    rw [h1]
    module) 2
  simp at h0
