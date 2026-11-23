-- Prove2me | solution 1 for SumProduct.conv_withDensity_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:54:43.388606+00:00
-- url     : https://prove2.me/submissions/0a73d193-db04-4db3-9548-e9cf2f3d83c8

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution
    (μ : Measure ℝ) [SFinite μ] {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    μ ∗ volume.withDensity f =
      volume.withDensity (fun z : ℝ => ∫⁻ x : ℝ, f (z - x) ∂μ) := by
  refine Measure.ext_of_lintegral _ ?_
  intro φ hφ
  rw [Measure.lintegral_conv hφ]
  rw [lintegral_withDensity_eq_lintegral_mul]
  · have hinner : ∀ x : ℝ,
        (∫⁻ y : ℝ, φ (x + y) ∂volume.withDensity f) =
          ∫⁻ y : ℝ, f y * φ (x + y) := by
      intro x
      rw [lintegral_withDensity_eq_lintegral_mul]
      · rfl
      · exact hf
      · exact hφ.comp (by fun_prop)
    simp_rw [hinner]
    have htranslate : ∀ x : ℝ,
        (∫⁻ y : ℝ, f y * φ (x + y)) =
          ∫⁻ a : ℝ, f (a - x) * φ a := by
      intro x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (MeasureTheory.lintegral_add_left_eq_self
          (μ := (volume : Measure ℝ)) (f := fun a : ℝ => f (a - x) * φ a) x)
    simp_rw [htranslate]
    rw [lintegral_lintegral_swap]
    · have hfactor : ∀ y : ℝ,
          (∫⁻ x : ℝ, f (y - x) * φ y ∂μ) =
            (∫⁻ x : ℝ, f (y - x) ∂μ) * φ y := by
        intro y
        rw [lintegral_mul_const'' (φ y)]
        exact (hf.comp (by fun_prop)).aemeasurable
      simp_rw [hfactor]
      rfl
    · fun_prop
  · fun_prop
  · exact hφ
end SumProduct
