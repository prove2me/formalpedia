-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.gm_integral_wvol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:33:36.758911+00:00
-- url     : https://prove2.me/submissions/d70911f6-1c77-41af-8174-a5548a60f635

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


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
variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : Measurable ph)
    (G : M → ℂ) :
    ∫ x, G x ∂wvol n z ph = ∫ x, (Real.exp (-ph x) : ℂ) * G x ∂vol n z ∧
      (Integrable G (wvol n z ph) → Integrable (fun x => (Real.exp (-ph x) : ℂ) * G x) (vol n z)) := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-ph x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hph.neg)
  have hlt : ∀ᵐ x ∂vol n z, ENNReal.ofReal (Real.exp (-ph x)) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hfun : (fun x => (ENNReal.ofReal (Real.exp (-ph x))).toReal • G x) =
      fun x => (Real.exp (-ph x) : ℂ) * G x := by
    funext x
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]
  refine ⟨?_, fun h => ?_⟩
  · rw [wvol, integral_withDensity_eq_integral_toReal_smul hm hlt, hfun]
  · rw [wvol, integrable_withDensity_iff_integrable_smul' hm hlt, hfun] at h
    exact h
end ReciprocityTheory.L2DbarEstimates.F
