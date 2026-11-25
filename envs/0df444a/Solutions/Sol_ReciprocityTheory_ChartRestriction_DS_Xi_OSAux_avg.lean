-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:10.525867+00:00
-- url     : https://prove2.me/submissions/c059d222-bafd-4b95-8be6-b41cfe108587

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LintegralInsertFiberLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DeZeroBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentConditionNeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ] (Φ : ℝ → X → X)
    (hΦm : Measurable (fun q : ℝ × X => Φ q.1 q.2))
    (hΦ : ∀ t ∈ Icc (1 : ℝ) 2, MeasurePreserving (Φ t) μ μ) {f w : X → ℝ≥0∞}
    (hf : Measurable f) (hw : Measurable w) (K : ℝ≥0∞)
    (hK : ∀ t ∈ Icc (1 : ℝ) 2, ∀ x, f (Φ t x) ≤ K * f x) :
    ∫⁻ x, f x * w x ∂μ ≤ K * ∫⁻ x, f x * (∫⁻ t in Icc (1 : ℝ) 2, w (Φ t x)) ∂μ := by
  have hvol : volume (Icc (1 : ℝ) 2) = 1 := by
    rw [Real.volume_Icc]; norm_num
  have hm2 : Measurable (fun q : ℝ × X => f q.2 * w (Φ q.1 q.2)) :=
    (hf.comp measurable_snd).mul (hw.comp hΦm)
  have hm3 : Measurable fun t : ℝ => ∫⁻ x, f x * w (Φ t x) ∂μ := hm2.lintegral_prod_right'
  calc ∫⁻ x, f x * w x ∂μ = ∫⁻ _t in Icc (1 : ℝ) 2, (∫⁻ x, f x * w x ∂μ) := by
        rw [setLIntegral_const, hvol, mul_one]
    _ ≤ ∫⁻ t in Icc (1 : ℝ) 2, K * (∫⁻ x, f x * w (Φ t x) ∂μ) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        calc ∫⁻ x, f x * w x ∂μ = ∫⁻ x, f (Φ t x) * w (Φ t x) ∂μ :=
              ((hΦ t ht).lintegral_comp (hf.mul hw)).symm
          _ ≤ ∫⁻ x, K * (f x * w (Φ t x)) ∂μ := lintegral_mono fun x => by
              rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hK t ht x) zero_le
          _ = K * ∫⁻ x, f x * w (Φ t x) ∂μ :=
              lintegral_const_mul K (hf.mul (hw.comp (hΦ t ht).measurable))
    _ = K * ∫⁻ t in Icc (1 : ℝ) 2, (∫⁻ x, f x * w (Φ t x) ∂μ) := lintegral_const_mul K hm3
    _ = K * ∫⁻ x, (∫⁻ t in Icc (1 : ℝ) 2, f x * w (Φ t x)) ∂μ := by
        rw [lintegral_lintegral_swap (f := fun t x => f x * w (Φ t x)) hm2.aemeasurable]
    _ = K * ∫⁻ x, f x * (∫⁻ t in Icc (1 : ℝ) 2, w (Φ t x)) ∂μ := by
        congr 1
        refine lintegral_congr fun x => ?_
        exact lintegral_const_mul (f x)
          ((show Measurable (Function.uncurry fun t x => w (Φ t x)) from hw.comp hΦm).of_uncurry_right)
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
