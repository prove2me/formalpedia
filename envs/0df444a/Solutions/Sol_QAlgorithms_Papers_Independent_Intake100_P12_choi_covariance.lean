-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P12.choi_covariance
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:26:47.180586+00:00
-- url     : https://prove2.me/submissions/9567f9a5-3a4f-4bd6-8b5d-d0da2f65e278

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Intake100.P12
  QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution {d : ℕ} (hd : 0 < d)
    (U A B : Matrix.unitaryGroup (Fin d) ℂ) :
    ((A : Op (Fin d)) ⊗ₖ (B : Op (Fin d))) * gateChoi (U : Op (Fin d)) *
      (((A : Op (Fin d)) ⊗ₖ (B : Op (Fin d)))ᴴ) =
    gateChoi ((A : Op (Fin d)) * (U : Op (Fin d)) * (B : Op (Fin d)).transpose) := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      M = (A : Op (Fin d)) ⊗ₖ (B : Op (Fin d)) := ⟨_, rfl⟩
  rw [← hM]
  have key : ∀ x : Fin d × Fin d, ∑ p, M x p * (U : Op (Fin d)) p.1 p.2
      = ((A : Op (Fin d)) * (U : Op (Fin d)) * (B : Op (Fin d)).transpose) x.1 x.2 := by
    intro x
    rw [hM]
    simp only [Matrix.kronecker_apply, Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_prod_type, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  ext x y
  show (M * gateChoi (U : Op (Fin d)) * Mᴴ) x y
    = ((A : Op (Fin d)) * (U : Op (Fin d)) * (B : Op (Fin d)).transpose) x.1 x.2 *
      conj (((A : Op (Fin d)) * (U : Op (Fin d)) * (B : Op (Fin d)).transpose) y.1 y.2)
  rw [← key x, ← key y, map_sum, Finset.sum_mul]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, gateChoi, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_)
  rw [map_mul, Complex.star_def]
  ring
