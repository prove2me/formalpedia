-- Prove2me | solution 1 for avram_w8_22_uniform_nu_integral_near_f5277180
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:32:19.690276+00:00
-- url     : https://prove2.me/submissions/d6315054-1052-434c-89aa-42dc621fa76a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_negative_levy_near_far_kernel_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

noncomputable section
theorem avram_w8_22_uniform_nu_integral_near_f5277180
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (w : ℝ → ℝ) (hwMeas : Measurable w)
  (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
  (hL : 0 ≤ L) (hR : 0 ≤ R)
  (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v|)
  (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
  (hMass : X.ν (Iic (-a / 2)) < ⊤) 
    (hGmeas : (let G : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z); Measurable G))
    (hSub : (let G : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z); Ioo (-a / 2) (0 : ℝ) ⊆ Ioo (-1) 0))
    (hFirst : (let G : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z); IntegrableOn (fun z : ℝ => -z) (Ioo (-a / 2) 0) X.ν))
    : (let G : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z); IntegrableOn G (Ioo (-a / 2) 0) X.ν) := by
  intro G
  have hEq : EqOn G (fun z : ℝ => L * (-z)) (Ioo (-a / 2) 0) := by
    intro z hz
    simp only [G]
    rw [if_neg (not_le.mpr hz.1)]
  exact IntegrableOn.congr_fun (Integrable.const_mul hFirst L) hEq.symm measurableSet_Ioo

theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (w : ℝ → ℝ) (hwMeas : Measurable w)
  (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
  (hL : 0 ≤ L) (hR : 0 ≤ R)
  (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v|)
  (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
  (hMass : X.ν (Iic (-a / 2)) < ⊤) 
    (hGmeas : (let G : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z); Measurable G))
    (hSub : (let G : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z); Ioo (-a / 2) (0 : ℝ) ⊆ Ioo (-1) 0))
    (hFirst : (let G : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z); IntegrableOn (fun z : ℝ => -z) (Ioo (-a / 2) 0) X.ν))
    : (let G : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z); IntegrableOn G (Ioo (-a / 2) 0) X.ν) := by
  intro G
  have hEq : EqOn G (fun z : ℝ => L * (-z)) (Ioo (-a / 2) 0) := by
    intro z hz
    simp only [G]
    rw [if_neg (not_le.mpr hz.1)]
  exact IntegrableOn.congr_fun (Integrable.const_mul hFirst L) hEq.symm measurableSet_Ioo

end

