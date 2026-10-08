-- Prove2me | solution 1 for PrimePairSieve.reciprocal_error_transfer_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T11:45:13.888984+00:00
-- url     : https://prove2.me/submissions/633ab6e9-c1e4-4641-a1a3-83e7514f6e26

import Theorems.Thm_PrimePairSieve_reciprocal_error_kernel_bounds
import Mathlib.Tactic

open Real MeasureTheory Set

noncomputable section
set_option autoImplicit false

private lemma kernel_continuous {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun t : ℝ => z / (z + t) ^ 2) (uIcc 0 z) := by
  apply continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
  intro t ht
  rw [uIcc_of_le hz.le] at ht
  exact pow_ne_zero 2 (ne_of_gt (by linarith [ht.1] : 0 < z + t))

private lemma scaled_kernel_integral {z : ℝ} (hz : 0 < z) :
    (∫ t in Ioc (0 : ℝ) z, z / (z + t) ^ 2 * t ^ (-(1 / 3 : ℝ))) =
      z ^ (-(1 / 3 : ℝ)) *
        (∫ s in Ioc (0 : ℝ) 1, s ^ (-(1 / 3 : ℝ)) / (1 + s) ^ 2) := by
  let g : ℝ → ℝ := fun t => z / (z + t) ^ 2 * t ^ (-(1 / 3 : ℝ))
  have hscale := intervalIntegral.mul_integral_comp_mul_left (f := g) z
    (a := 0) (b := 1)
  simp only [mul_zero, mul_one] at hscale
  rw [← intervalIntegral.integral_of_le hz.le,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← hscale]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  dsimp [g]
  rw [Real.mul_rpow hz.le hs.1]
  have hden : 1 + s ≠ 0 := ne_of_gt (by linarith [hs.1])
  field_simp [hz.ne', hden]

theorem solution
    (f : ℝ → ℝ) (z E : ℝ) (hz : 0 < z) (hE : 0 ≤ E)
    (hfint : IntegrableOn f (Ioc 0 z))
    (hf : ∀ t ∈ Ioc 0 z, |f t| ≤ E * t ^ (-(1 / 3 : ℝ))) :
    |f z / 2 + ∫ t in Ioc 0 z, z / (z + t) ^ 2 * f t| ≤
      (8479 / 6160 : ℝ) * E * z ^ (-(1 / 3 : ℝ)) := by
  have hfi : IntervalIntegrable f volume 0 z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mpr hfint
  have hwi : IntegrableOn (fun t => z / (z + t) ^ 2 * f t) (Ioc 0 z) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mp
    simpa only [mul_comm] using hfi.mul_continuousOn (kernel_continuous hz)
  have hpi : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 3 : ℝ))) volume 0 z :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hbi : IntegrableOn (fun t => z / (z + t) ^ 2 * (E * t ^ (-(1 / 3 : ℝ))))
      (Ioc 0 z) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mp
    simpa only [mul_comm] using
      (hpi.const_mul E).mul_continuousOn (kernel_continuous hz)
  have hibound : |∫ t in Ioc 0 z, z / (z + t) ^ 2 * f t| ≤
      E * z ^ (-(1 / 3 : ℝ)) * (5399 / 6160) := by
    calc
      _ ≤ ∫ t in Ioc 0 z, |z / (z + t) ^ 2 * f t| := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (f := fun t => z / (z + t) ^ 2 * f t)
            (μ := volume.restrict (Ioc 0 z)))
      _ ≤ ∫ t in Ioc 0 z, z / (z + t) ^ 2 * (E * t ^ (-(1 / 3 : ℝ))) := by
        apply integral_mono_ae hwi.norm hbi
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have hk : 0 ≤ z / (z + t) ^ 2 := div_nonneg hz.le (sq_nonneg _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
        exact mul_le_mul_of_nonneg_left (hf t ht) hk
      _ = E * (z ^ (-(1 / 3 : ℝ)) *
          (∫ s in Ioc (0 : ℝ) 1, s ^ (-(1 / 3 : ℝ)) / (1 + s) ^ 2)) := by
        simp_rw [show ∀ t : ℝ, z / (z + t) ^ 2 * (E * t ^ (-(1 / 3 : ℝ))) =
          E * (z / (z + t) ^ 2 * t ^ (-(1 / 3 : ℝ))) from fun t => by ring]
        rw [integral_const_mul, scaled_kernel_integral hz]
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left PrimePairSieve.reciprocal_error_kernel_bounds.2
          (mul_nonneg hE (Real.rpow_nonneg hz.le _))
  have hend : |f z / 2| ≤ E * z ^ (-(1 / 3 : ℝ)) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (hf z ⟨hz, le_rfl⟩) (by norm_num)
  calc
    _ ≤ |f z / 2| + |∫ t in Ioc 0 z, z / (z + t) ^ 2 * f t| := abs_add_le _ _
    _ ≤ E * z ^ (-(1 / 3 : ℝ)) / 2 + E * z ^ (-(1 / 3 : ℝ)) * (5399 / 6160) :=
      add_le_add hend hibound
    _ = _ := by ring

#print axioms solution
