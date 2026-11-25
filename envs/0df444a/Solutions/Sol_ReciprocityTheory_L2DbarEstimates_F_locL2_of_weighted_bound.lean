-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.locL2_of_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:46.14009+00:00
-- url     : https://prove2.me/submissions/db00c568-d571-499e-a378-f6c3c5d74cfa

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
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
theorem _root_.solution {M E : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [BorelSpace M] [NormedAddCommGroup E]
    (μ : Measure M) (u : M → E) (q ph : M → ℝ) (c : ℝ) (hc : 0 ≤ c) (hph : Continuous ph)
    (hu : AEStronglyMeasurable u μ) (hq : ∀ x, ‖u x‖ ^ 2 ≤ c * q x)
    (h : ∫⁻ x, ENNReal.ofReal (q x * Real.exp (-ph x)) ∂μ < ⊤) : LocalL2Isometry μ u := by
  unfold LocalL2Isometry
  refine ⟨hu, fun C hC => ?_⟩
  obtain ⟨K, hK⟩ := hC.bddAbove_image hph.continuousOn
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hpt : ∀ x ∈ C, ‖u x‖ₑ ^ 2 ≤
      ENNReal.ofReal (c * Real.exp K) * ENNReal.ofReal (q x * Real.exp (-ph x)) := by
    intro x hx
    have hphK : ph x ≤ K := hK ⟨x, hx, rfl⟩
    have hE : Real.exp (ph x) ≤ Real.exp K := Real.exp_le_exp.2 hphK
    have hF : 0 < Real.exp (-ph x) := Real.exp_pos _
    have hEF : Real.exp (ph x) * Real.exp (-ph x) = 1 := by
      rw [← Real.exp_add]
      simp
    have hcq : 0 ≤ c * q x := le_trans (sq_nonneg _) (hq x)
    have hEF' : c * q x * (Real.exp (ph x) * Real.exp (-ph x)) = c * q x := by
      rw [hEF, mul_one]
    have hprod := mul_nonneg (mul_nonneg hcq hF.le) (sub_nonneg.2 hE)
    have hq' := hq x
    have hb : ‖u x‖ ^ 2 ≤ (c * Real.exp K) * (q x * Real.exp (-ph x)) := by
      nlinarith [hEF', hprod, hq']
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg hc (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hb
  calc ∫⁻ x in C, ‖u x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in C, ENNReal.ofReal (c * Real.exp K) * ENNReal.ofReal (q x * Real.exp (-ph x)) ∂μ := by
        first
        | exact setLIntegral_mono' hCm hpt
        | exact lintegral_mono_ae ((ae_restrict_iff' hCm).2 (ae_of_all _ hpt))
    _ = ENNReal.ofReal (c * Real.exp K) * ∫⁻ x in C, ENNReal.ofReal (q x * Real.exp (-ph x)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (c * Real.exp K) * ∫⁻ x, ENNReal.ofReal (q x * Real.exp (-ph x)) ∂μ := by
        gcongr
        first
        | exact Measure.restrict_le_self
        | exact setLIntegral_le_lintegral _ _
        | exact lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h
end ReciprocityTheory.L2DbarEstimates.F
