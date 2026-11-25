-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_k__nonneg_95fdb6d5ed2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:44.56135+00:00
-- url     : https://prove2.me/submissions/d0ca7647-70b1-4d5f-b7db-c1a58705a945

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
theorem _root_.solution (x : ℝ) : 0 ≤ kθ x := by
  unfold kθ
  exact ContDiffBump.nonneg_normed _ x
end ReciprocityTheory.AnForm.A
