-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.lipschitz_tmax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:02.471044+00:00
-- url     : https://prove2.me/submissions/8a12ef5b-0e9c-47d2-b822-7cef0cdb8d93

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_tmax_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : LipschitzWith 1 (tmax : (ι → ℝ) → ℝ) := LipschitzWith.of_dist_le_mul fun s t => by
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  exact abs_tmax_sub_le s t
end ReciprocityTheory.AnForm.A
