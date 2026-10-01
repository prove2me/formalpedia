-- Prove2me | solution 1 for burau_rho_mul_Sm_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-10-01T00:07:10.363945+00:00
-- url     : https://prove2.me/submissions/d2c7879b-9379-49cb-a5c2-5ecf1420a9ae

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_reduced_braid_group

set_option autoImplicit false

open Matrix

namespace BurauNC

theorem mul_Sm_of_zero_ (M : M2) (h0 : M 0 0 = 0) :
    M * Sm = !![M 0 1, 0; M 1 1, -(M 1 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sm, Matrix.mul_apply, Fin.sum_univ_two, h0]

end BurauNC

/-- **S-rule, zero case**: if `M 0 0 = 0` (so `M = !![0,±1;∓1,d]` up to unimodularity) then
`rho (M * S) = baseQ ((M*S)*S) * liftS⁻¹`. -/
theorem solution (M : BurauNC.M2) (hd : M.det = 1) (h0 : M 0 0 = 0) :
    BurauNC.rho (M * BurauNC.Sm) =
      BurauNC.baseQ (M * BurauNC.Sm * BurauNC.Sm) * BurauNC.liftS⁻¹ := by
  have hdet : M 0 1 * M 1 0 = -1 := by
    have h2 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      simpa [Matrix.det_fin_two] using hd
    rw [h0] at h2
    simp only [zero_mul, zero_sub] at h2
    linarith
  have hone : M 0 1 * (-(M 1 0)) = 1 := by
    rw [mul_neg, hdet]
    ring
  have hMS : M * BurauNC.Sm = !![M 0 1, 0; M 1 1, -(M 1 0)] := BurauNC.mul_Sm_of_zero_ M h0
  have h00 : (M * BurauNC.Sm) 0 0 = M 0 1 := by rw [hMS]; simp
  have h01 : (M * BurauNC.Sm) 0 1 = 0 := by rw [hMS]; simp
  have hnat : ((M * BurauNC.Sm) 0 0).natAbs = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hone with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h00, h1]; rfl
    · rw [h00, h1]; rfl
  have hne : ¬ ((M * BurauNC.Sm) 0 0 = 0) := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hone with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h00, h1]; norm_num
    · rw [h00, h1]; norm_num
  rw [BurauNC.rho, hnat]
  simp only [BurauNC.rhoIter, if_neg hne]
  rw [h01, Int.zero_ediv, neg_zero, BurauNC.Tm, ← Matrix.one_fin_two, mul_one, zpow_zero, mul_one]
