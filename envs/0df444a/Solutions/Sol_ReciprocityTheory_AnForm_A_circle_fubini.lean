-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.circle_fubini
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:09.37569+00:00
-- url     : https://prove2.me/submissions/71f7914e-fef8-404d-9037-f6d4fc7fb39c

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set Real
open scoped ContDiff
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {Φ : (Fin D → ℂ) → ℝ} (hΦm : Measurable Φ) (hΦi : Integrable Φ)
    {k : (Fin D → ℂ) → ℝ} (hk : Continuous k) (hkc : HasCompactSupport k)
    {P : ℂ → (Fin D → ℂ) → (Fin D → ℂ)} (hP : Continuous (Function.uncurry P))
    (hPm : ∀ ζ : ℂ, ‖ζ‖ = 1 → MeasurePreserving (P ζ) ∧ MeasurableEmbedding (P ζ)) :
    Integrable (fun y => k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1) ∧
    ∫ y, k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1 =
      circleAverage (fun ζ => ∫ y, k y * Φ (P ζ y)) 0 1 := by
  obtain ⟨M, hM⟩ := hk.bounded_above_of_compact_support hkc
  set μθ : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hμθ
  set f : ℝ → (Fin D → ℂ) → ℝ := fun θ y => k y * Φ (P (circleMap 0 1 θ) y) with hf
  have hcm : ∀ θ, ‖circleMap 0 1 θ‖ = 1 := fun θ => by simp
  have hfm : Measurable (Function.uncurry f) := by
    have h1 : Continuous fun q : ℝ × (Fin D → ℂ) => P (circleMap 0 1 q.1) q.2 :=
      hP.comp (((continuous_circleMap 0 1).comp continuous_fst).prodMk continuous_snd)
    exact (hk.measurable.comp measurable_snd).mul (hΦm.comp h1.measurable)
  have hsec : ∀ θ, Integrable (f θ) ∧ ∫ y, ‖f θ y‖ ≤ M * ∫ y, |Φ y| := by
    intro θ
    obtain ⟨he, hee⟩ := hPm _ (hcm θ)
    have hi : Integrable fun y => Φ (P (circleMap 0 1 θ) y) :=
      (he.integrable_comp_emb hee).2 hΦi
    have hint : Integrable (f θ) :=
      hi.bdd_mul hk.aestronglyMeasurable (Eventually.of_forall hM)
    refine ⟨hint, ?_⟩
    calc ∫ y, ‖f θ y‖ ≤ ∫ y, M * |Φ (P (circleMap 0 1 θ) y)| := by
          refine integral_mono hint.norm (hi.abs.const_mul M) fun y => ?_
          simp only [hf, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hM y) (abs_nonneg _)
      _ = M * ∫ y, |Φ y| := by
          rw [integral_const_mul, he.integral_comp hee (fun y => |Φ y|)]
  have hint : Integrable (Function.uncurry f) (μθ.prod volume) := by
    rw [integrable_prod_iff hfm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun θ => (hsec θ).1, ?_⟩
    refine Integrable.mono' (integrable_const (M * ∫ y, |Φ y|)) ?_
      (Eventually.of_forall fun θ => ?_)
    · exact hfm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hsec θ).2
  have hswap := integral_integral_swap hint
  have hpt : ∀ y, k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1 =
      (2 * π)⁻¹ * ∫ θ, f θ y ∂μθ := by
    intro y
    rw [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le,
      mul_left_comm, ← integral_const_mul]
  refine ⟨?_, ?_⟩
  · simp_rw [hpt]
    exact hint.integral_prod_right.const_mul _
  calc ∫ y, k y * circleAverage (fun ζ => Φ (P ζ y)) 0 1
      = ∫ y, (2 * π)⁻¹ * ∫ θ, f θ y ∂μθ := by simp_rw [hpt]
    _ = (2 * π)⁻¹ * ∫ θ, ∫ y, f θ y ∂volume ∂μθ := by rw [integral_const_mul, hswap]
    _ = circleAverage (fun ζ => ∫ y, k y * Φ (P ζ y)) 0 1 := by
        rw [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le]
end ReciprocityTheory.AnForm.A
