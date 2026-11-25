-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.integrable_of_continuous_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:30:55.272857+00:00
-- url     : https://prove2.me/submissions/30b50af5-6425-4e3b-aae0-978e9ef75bc8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integrable_of_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (vol n z) := by
  have h := integrable_of_continuous n z hz (fun x => (f x : ℂ)) (Complex.continuous_ofReal.comp hf)
    (hc.comp_left Complex.ofReal_zero)
  simpa using h.re
end ReciprocityTheory.L2DbarEstimates
