-- Prove2me | solution 1 for burau_rho_mul_Sm_terminal
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-10-01T00:18:58.282371+00:00
-- url     : https://prove2.me/submissions/da61c41a-9cc7-4fe4-9bb4-9dd7237da45e

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_reduced_braid_group
import Theorems.Thm_burau_rho_mul_Sm_of_zero
import Theorems.Thm_burau_liftS_pow_four
import Theorems.Thm_burau_liftS_sq_central

set_option autoImplicit false

open Matrix

namespace BurauNC

theorem mul_Sm_Sm_ (M : M2) : M * Sm * Sm = -M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem liftS_cube_ : liftS ^ 3 = liftS⁻¹ := by
  have h : liftS * liftS ^ 3 = 1 := by
    rw [← pow_succ', burau_liftS_pow_four]
  exact (inv_eq_of_mul_eq_one_right h).symm

theorem liftS_conj1_ (X : Q) : liftS ^ 3 * X * liftS⁻¹ = liftS * X * liftS := by
  have hc : X * liftS ^ 2 = liftS ^ 2 * X := Subgroup.mem_center_iff.mp burau_liftS_sq_central X
  have h3 : liftS ^ 3 = liftS * liftS ^ 2 := by group
  rw [h3]
  calc liftS * liftS ^ 2 * X * liftS⁻¹ = liftS * (liftS ^ 2 * X) * liftS⁻¹ := by group
    _ = liftS * (X * liftS ^ 2) * liftS⁻¹ := by rw [← hc]
    _ = liftS * X * liftS := by group

theorem liftS_conj2_ (X : Q) : liftS * X * liftS⁻¹ = liftS ^ 3 * X * liftS := by
  have hc : X * liftS ^ 2 = liftS ^ 2 * X := Subgroup.mem_center_iff.mp burau_liftS_sq_central X
  have h3 : liftS ^ 3 = liftS * liftS ^ 2 := by group
  calc liftS * X * liftS⁻¹ = liftS * X * liftS ^ 3 := by rw [← liftS_cube_]
    _ = liftS * X * (liftS * liftS ^ 2) := by rw [h3]
    _ = liftS * (X * liftS ^ 2) * liftS := by group
    _ = liftS * (liftS ^ 2 * X) * liftS := by rw [← hc]
    _ = liftS ^ 3 * X * liftS := by rw [h3]; group

end BurauNC

/-- **S-rule, terminal case** `M 0 0 = 0`: `rho (M * S) = rho M * liftS`. -/
theorem solution (M : BurauNC.M2) (hd : M.det = 1) (h0 : M 0 0 = 0) :
    BurauNC.rho (M * BurauNC.Sm) = BurauNC.rho M * BurauNC.liftS := by
  have hone : M 0 1 * (-(M 1 0)) = 1 := by
    have hdet : M 0 1 * M 1 0 = -1 := by
      have h2 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
        simpa [Matrix.det_fin_two] using hd
      rw [h0] at h2
      simp only [zero_mul, zero_sub] at h2
      linarith
    rw [mul_neg, hdet]
    ring
  have hM : BurauNC.rho M = BurauNC.baseQ M := by
    simp only [BurauNC.rho, h0, Int.natAbs_zero, BurauNC.rhoIter]
  rw [burau_rho_mul_Sm_of_zero M hd h0, hM, BurauNC.mul_Sm_Sm_ M]
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hone with ⟨h1, _⟩ | ⟨h1, _⟩
  · have hbM : BurauNC.baseQ M = BurauNC.liftS ^ 3 * BurauNC.liftT ^ (-(M 1 1)) := by
      rw [BurauNC.baseQ, if_neg (by rw [h1]; norm_num)]
    have hbN : BurauNC.baseQ (-M) = BurauNC.liftS * BurauNC.liftT ^ (-(M 1 1)) := by
      rw [BurauNC.baseQ, if_pos (by simp [h1])]
      simp
    rw [hbN, hbM]
    exact BurauNC.liftS_conj2_ (BurauNC.liftT ^ (-(M 1 1)))
  · have hbM : BurauNC.baseQ M = BurauNC.liftS * BurauNC.liftT ^ (M 1 1) := by
      rw [BurauNC.baseQ, if_pos (by rw [h1])]
    have hbN : BurauNC.baseQ (-M) = BurauNC.liftS ^ 3 * BurauNC.liftT ^ (M 1 1) := by
      rw [BurauNC.baseQ, if_neg (by simp [h1])]
      simp
    rw [hbN, hbM]
    exact BurauNC.liftS_conj1_ (BurauNC.liftT ^ (M 1 1))
