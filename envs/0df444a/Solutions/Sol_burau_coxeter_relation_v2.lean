-- Prove2me | solution 1 for burau_coxeter_relation_v2
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T23:13:37.659229+00:00
-- url     : https://prove2.me/submissions/d0eca4ea-a617-4edb-8847-6cf736a60963

import Definitions.Def_burau_reduced_braid_group
import Theorems.Thm_burau_liftS_pow_four
import Theorems.Thm_burau_liftU_cube
import Theorems.Thm_burau_liftS_sq_central

set_option autoImplicit false

/-- **Coxeter relation** `(liftS⁻¹ * liftT) ^ 3 = 1` in `Q = B₃ ⧸ ⟨⟨Δ₄⟩⟩`, self-contained version. -/
theorem solution : (BurauNC.liftS⁻¹ * BurauNC.liftT) ^ 3 = 1 := by
  have liftS_sq_comm : ∀ x : BurauNC.Q, BurauNC.liftS ^ 2 * x = x * BurauNC.liftS ^ 2 :=
    fun x => (Subgroup.mem_center_iff.mp burau_liftS_sq_central x).symm
  set a := BurauNC.liftS⁻¹ * BurauNC.liftT with ha
  have hcc : BurauNC.liftS ^ 2 * BurauNC.liftS ^ 2 = 1 := by
    rw [show BurauNC.liftS ^ 2 * BurauNC.liftS ^ 2 = BurauNC.liftS ^ 4 by group]
    exact burau_liftS_pow_four
  have hfac : BurauNC.liftS * a * BurauNC.liftS
      = (BurauNC.liftS * a * BurauNC.liftS⁻¹) * BurauNC.liftS ^ 2 := by
    rw [show BurauNC.liftS * a * BurauNC.liftS⁻¹ * BurauNC.liftS ^ 2
        = BurauNC.liftS * a * (BurauNC.liftS⁻¹ * BurauNC.liftS ^ 2) by group]
    rw [show BurauNC.liftS⁻¹ * BurauNC.liftS ^ 2 = BurauNC.liftS by group]
  have h3 : (BurauNC.liftS * a * BurauNC.liftS) ^ 3 = BurauNC.liftS ^ 2 := by
    have hu : BurauNC.liftT * BurauNC.liftS = BurauNC.liftS * a * BurauNC.liftS := by
      rw [ha]
      group
    rw [← hu]
    exact burau_liftU_cube
  have h3' : ((BurauNC.liftS * a * BurauNC.liftS⁻¹) * BurauNC.liftS ^ 2) ^ 3
      = BurauNC.liftS ^ 2 := by
    rw [← hfac]
    exact h3
  have hcomm : Commute (BurauNC.liftS * a * BurauNC.liftS⁻¹) (BurauNC.liftS ^ 2) :=
    (liftS_sq_comm (BurauNC.liftS * a * BurauNC.liftS⁻¹)).symm
  rw [Commute.mul_pow hcomm] at h3'
  have hcube' : (BurauNC.liftS * a * BurauNC.liftS⁻¹) ^ 3
      = BurauNC.liftS * a ^ 3 * BurauNC.liftS⁻¹ := by
    rw [pow_three, pow_three]
    group
  have hs6 : (BurauNC.liftS ^ 2) ^ 3 = BurauNC.liftS ^ 2 := by
    rw [show (BurauNC.liftS ^ 2) ^ 3 = BurauNC.liftS ^ 2 * BurauNC.liftS ^ 4 by group,
      burau_liftS_pow_four, mul_one]
  rw [hcube', hs6] at h3'
  have hX : BurauNC.liftS * a ^ 3 * BurauNC.liftS⁻¹ = 1 := by
    calc BurauNC.liftS * a ^ 3 * BurauNC.liftS⁻¹
        = (BurauNC.liftS * a ^ 3 * BurauNC.liftS⁻¹) * (BurauNC.liftS ^ 2 * BurauNC.liftS ^ 2) := by
          rw [hcc, mul_one]
      _ = ((BurauNC.liftS * a ^ 3 * BurauNC.liftS⁻¹) * BurauNC.liftS ^ 2) * BurauNC.liftS ^ 2 := by
          group
      _ = BurauNC.liftS ^ 2 * BurauNC.liftS ^ 2 := by rw [h3']
      _ = 1 := hcc
  calc a ^ 3 = BurauNC.liftS⁻¹ * (BurauNC.liftS * a ^ 3 * BurauNC.liftS⁻¹) * BurauNC.liftS := by
        group
    _ = BurauNC.liftS⁻¹ * 1 * BurauNC.liftS := by rw [hX]
    _ = 1 := by group
