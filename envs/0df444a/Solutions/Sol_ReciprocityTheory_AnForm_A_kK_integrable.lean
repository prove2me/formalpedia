-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.kK_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:51.488809+00:00
-- url     : https://prove2.me/submissions/405704fa-2c4f-4d75-af9a-87823e78d79a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_hasCompactSupport

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
theorem _root_.solution : Integrable (kK : (ι → ℝ) → ℝ) := kK_contDiff.continuous.integrable_of_hasCompactSupport kK_hasCompactSupport
end ReciprocityTheory.AnForm.A
