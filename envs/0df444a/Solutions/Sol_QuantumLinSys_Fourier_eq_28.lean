-- Prove2me | solution 1 for QuantumLinSys.Fourier.eq_28
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-10T02:09:03.881243+00:00
-- url     : https://prove2.me/submissions/97974c9f-8cc5-436a-83c2-13bd4480fe24

import Mathlib
import Definitions.Def_QuantumLinSys_Fourier_Setting

open MeasureTheory

/-- Translating a half-line integral to the half-line at the origin. -/
lemma shift_Ioi_eq28 (a : ℝ) (g : ℝ → ℝ) :
    ∫ z in Set.Ioi a, g (z - a) = ∫ t in Set.Ioi (0 : ℝ), g t := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_sub_right_eq_self (fun z => (Set.Ioi (0 : ℝ)).indicator g z) a]
  congr 1
  funext z
  simp only [Set.indicator, Set.mem_Ioi, sub_pos]

theorem solution (zK : ℝ) (hz : 0 ≤ zK) :
    1 / Real.sqrt (2 * Real.pi) *
      ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) ≤
        1 / 2 * Real.exp (-zK ^ 2 / 2) := by
  have hpi := Real.pi_pos
  -- pointwise domination
  have hpt : ∀ z ∈ Set.Ioi zK, Real.exp (-z ^ 2 / 2) ≤
      Real.exp (-zK ^ 2 / 2) * Real.exp (-(1 / 2) * (z - zK) ^ 2) := by
    intro z hz'
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : zK < z := hz'
    nlinarith
  -- integrability
  have hg : Integrable (fun t : ℝ => Real.exp (-(1 / 2) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hint1 : IntegrableOn (fun z => Real.exp (-z ^ 2 / 2)) (Set.Ioi zK) := by
    have : (fun z : ℝ => Real.exp (-z ^ 2 / 2)) = fun z => Real.exp (-(1 / 2) * z ^ 2) := by
      funext z; congr 1; ring
    rw [this]; exact hg.integrableOn
  have hint2 : IntegrableOn
      (fun z => Real.exp (-zK ^ 2 / 2) * Real.exp (-(1 / 2) * (z - zK) ^ 2)) (Set.Ioi zK) :=
    ((hg.comp_sub_right zK).const_mul _).integrableOn
  -- the shifted Gaussian integral
  have hshift : ∫ z in Set.Ioi zK, Real.exp (-(1 / 2) * (z - zK) ^ 2) =
      Real.sqrt (2 * Real.pi) / 2 := by
    rw [shift_Ioi_eq28 zK (fun t => Real.exp (-(1 / 2) * t ^ 2)), integral_gaussian_Ioi]
    congr 2; try field_simp
  have hmono : ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) ≤
      ∫ z in Set.Ioi zK, Real.exp (-zK ^ 2 / 2) * Real.exp (-(1 / 2) * (z - zK) ^ 2) :=
    setIntegral_mono_on hint1 hint2 measurableSet_Ioi hpt
  rw [integral_const_mul, hshift] at hmono
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  calc 1 / Real.sqrt (2 * Real.pi) * ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2)
      ≤ 1 / Real.sqrt (2 * Real.pi) * (Real.exp (-zK ^ 2 / 2) * (Real.sqrt (2 * Real.pi) / 2)) := by
        gcongr
    _ = 1 / 2 * Real.exp (-zK ^ 2 / 2) := by field_simp; try ring
