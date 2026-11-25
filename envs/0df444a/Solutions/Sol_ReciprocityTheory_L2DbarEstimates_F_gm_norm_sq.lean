-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.gm_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:43:20.255912+00:00
-- url     : https://prove2.me/submissions/5e350b6c-456f-46b5-8965-70941101f9ee

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
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
variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] {μ : Measure M} (u : Lp E 2 μ) :
    ENNReal.ofReal (‖u‖ ^ 2) = ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂μ := by
  rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top u),
    eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num
end ReciprocityTheory.L2DbarEstimates.F
