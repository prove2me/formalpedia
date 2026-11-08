-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P41.projectedCoefficientProduct
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:34:15.057205+00:00
-- url     : https://prove2.me/submissions/dc69737a-abfd-4a4e-8182-b83f003354ed

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators

open MeasureTheory Set

open QAlgorithms.Papers.Independent.Intakenext100.P41 in
theorem solution {d : ℕ} (A : BasicODEData d) (i : Fin d) (n : ℕ) :
    projectedCoefficient A i n = A.phi (A.xi i) *
      ∏ m ∈ Finset.range n,
        resolventScalar A.P A.v A.phi (A.lambda i + ((m + 1 : ℕ) : ℂ)) := by
  have hQ : ∀ x : Fin d → ℂ, (linearRankOneMatrix A.v A.phi).mulVec x = A.phi x • A.v := by
    intro x
    ext k
    rw [LinearMap.pi_apply_eq_sum_univ A.phi x]
    simp only [Matrix.mulVec, dotProduct, linearRankOneMatrix, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have : (fun l => if j = l then (1 : ℂ) else 0) = Pi.single j 1 := by
      funext l; simp [Pi.single_apply, eq_comm]
    rw [this]; ring
  induction n with
  | zero => simp [projectedCoefficient, frobeniusPair]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
    unfold projectedCoefficient
    rw [frobeniusPair]
    simp only [hQ, Matrix.mulVec_smul, map_add, map_smul, resolventScalar, smul_eq_mul]
    ring
