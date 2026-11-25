-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integrable_mul_kK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:41.105617+00:00
-- url     : https://prove2.me/submissions/259efafd-875f-4738-9a02-eec0e4d800d9

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
theorem _root_.solution {g : (ι → ℝ) → ℝ} (hg : Continuous g) :
    Integrable (fun h => g h * kK h) := by
  first
    | exact (hg.mul kK_contDiff.continuous).integrable_of_hasCompactSupport kK_hasCompactSupport.mul_left
    | exact (hg.mul kK_contDiff.continuous).integrable_of_hasCompactSupport kK_hasCompactSupport.mul_right
end ReciprocityTheory.AnForm.A
