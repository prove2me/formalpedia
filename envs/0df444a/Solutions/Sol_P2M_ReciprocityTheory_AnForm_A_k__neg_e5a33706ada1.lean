-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_k__neg_e5a33706ada1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:40.495622+00:00
-- url     : https://prove2.me/submissions/61e00c65-7fbf-40e8-96f5-e65d845723e4

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift

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
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (x : ℝ) : kθ (-x) = kθ x := by
  unfold kθ
  exact ContDiffBump.normed_neg _ x
end ReciprocityTheory.AnForm.A
