-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.tmax_eq_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:55.750118+00:00
-- url     : https://prove2.me/submissions/044898db-8a41-4085-ae2c-df223b938111

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le

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
theorem _root_.solution {t : ι → ℝ} {i : ι} (h : ∀ j, t j ≤ t i) : tmax t = t i := le_antisymm (tmax_le h) (le_tmax t i)
end ReciprocityTheory.AnForm.A
