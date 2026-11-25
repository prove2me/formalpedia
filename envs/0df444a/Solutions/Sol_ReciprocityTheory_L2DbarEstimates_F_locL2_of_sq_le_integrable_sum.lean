-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.locL2_of_sq_le_integrable_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:14:28.47433+00:00
-- url     : https://prove2.me/submissions/aab3958f-e62c-4e18-98b5-6e6a1398eeb0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
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
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] (u : M → E)
    (hu : AEStronglyMeasurable u (vol n z))
    (c F1 F2 : M → ℝ) (hc : Continuous c) (hF1 : ∀ x, 0 ≤ F1 x) (hF2 : ∀ x, 0 ≤ F2 x)
    (hF1m : AEMeasurable (fun x => ENNReal.ofReal (F1 x)) (vol n z))
    (hI1 : ∫⁻ x, ENNReal.ofReal (F1 x) ∂vol n z < ⊤)
    (hI2 : ∫⁻ x, ENNReal.ofReal (F2 x) ∂vol n z < ⊤)
    (hb : ∀ x, ‖u x‖ ^ 2 ≤ c x * (F1 x + F2 x)) : LocalL2Isometry (vol n z) u := by
  refine ⟨hu, fun C hC => ?_⟩
  obtain ⟨K, hK⟩ := hC.bddAbove_image hc.continuousOn
  have hK' : ∀ x ∈ C, c x ≤ max K 0 := fun x hx =>
    (hK (Set.mem_image_of_mem c hx)).trans (le_max_left _ _)
  calc ∫⁻ x in C, ‖u x‖ₑ ^ 2 ∂vol n z
      ≤ ∫⁻ x in C, ENNReal.ofReal (max K 0) * (ENNReal.ofReal (F1 x) + ENNReal.ofReal (F2 x))
          ∂vol n z := by
        refine setLIntegral_mono' hC.measurableSet fun x hx => ?_
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_add (hF1 x) (hF2 x), ← ENNReal.ofReal_mul (le_max_right _ _)]
        apply ENNReal.ofReal_le_ofReal
        calc ‖u x‖ ^ 2 ≤ c x * (F1 x + F2 x) := hb x
          _ ≤ max K 0 * (F1 x + F2 x) :=
            mul_le_mul_of_nonneg_right (hK' x hx) (add_nonneg (hF1 x) (hF2 x))
    _ ≤ ∫⁻ x, ENNReal.ofReal (max K 0) * (ENNReal.ofReal (F1 x) + ENNReal.ofReal (F2 x))
          ∂vol n z := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (max K 0) *
          (∫⁻ x, ENNReal.ofReal (F1 x) ∂vol n z + ∫⁻ x, ENNReal.ofReal (F2 x) ∂vol n z) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hF1m]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hI1, hI2⟩)
end ReciprocityTheory.L2DbarEstimates.F
