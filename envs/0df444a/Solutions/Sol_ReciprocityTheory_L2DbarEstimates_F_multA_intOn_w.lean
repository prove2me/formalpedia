-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.multA_intOn_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:57:12.430082+00:00
-- url     : https://prove2.me/submissions/32fced07-545e-4ae1-9386-421ee2519e84

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableOnCompactOfLocL2
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_multA_integrable_of_sq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [OpensMeasurableSpace M] (μ : Measure M) [IsFiniteMeasureOnCompacts μ]
    (u : M → ℂ) (ph : M → ℝ) (hph : Continuous ph) (hu : AEStronglyMeasurable u μ)
    (h : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ < ⊤)
    (K : Set M) (hK : IsCompact K) : IntegrableOn u K μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hph.continuousOn
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  refine multA_integrable_of_sq (μ.restrict K) u hu.restrict ?_
  have hpt : ∀ x ∈ K, ‖u x‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) := by
    intro x hx
    have hx' : ph x ≤ C := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC x hx)
    have h1 : 1 ≤ Real.exp C * Real.exp (-ph x) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (Real.exp_pos C).le]
    apply ENNReal.ofReal_le_ofReal
    calc ‖u x‖ ^ 2 = ‖u x‖ ^ 2 * 1 := by ring
      _ ≤ ‖u x‖ ^ 2 * (Real.exp C * Real.exp (-ph x)) := by gcongr
      _ = Real.exp C * (‖u x‖ ^ 2 * Real.exp (-ph x)) := by ring
  calc ∫⁻ x in K, ‖u x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in K, ENNReal.ofReal (Real.exp C) *
          ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ :=
        setLIntegral_mono_ae' hK.measurableSet (Eventually.of_forall hpt)
    _ = ENNReal.ofReal (Real.exp C) *
          ∫⁻ x in K, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp C) *
          ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ := by
        gcongr; exact Measure.restrict_le_self
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h
end ReciprocityTheory.L2DbarEstimates.F
