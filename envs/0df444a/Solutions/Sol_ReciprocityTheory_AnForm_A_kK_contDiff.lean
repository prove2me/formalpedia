-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.kK_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:06.599204+00:00
-- url     : https://prove2.me/submissions/c12ad8e8-c19c-4ce0-8369-deb9aad9ff6f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__contDiff_6418abd5f35f

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
theorem _root_.solution : ContDiff ℝ ∞ (kK : (ι → ℝ) → ℝ) := by
  show ContDiff ℝ ∞ (fun h : ι → ℝ => ∏ j, kθ (h j))
  exact contDiff_prod fun j _ => kθ_contDiff.comp (contDiff_apply ℝ ℝ j)
end ReciprocityTheory.AnForm.A
