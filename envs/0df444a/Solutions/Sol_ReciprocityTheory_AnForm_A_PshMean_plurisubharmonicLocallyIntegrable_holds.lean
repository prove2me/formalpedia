-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMean.plurisubharmonicLocallyIntegrable_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:25.341137+00:00
-- url     : https://prove2.me/submissions/e2f545d9-2f50-48e5-96e8-8e748f9371de

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_subMeanValuePolydisc_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMean
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.PshMean
theorem _root_.solution : IsPsh_locallyIntegrableStatement := by
  intro D U φ hU hφ x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨closedBall x (r / 2), mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)),
    (subMeanValuePolydisc_holds D U φ x (r / 2) hU hφ (half_pos hr)
      ((closedBall_subset_ball (by linarith)).trans hrU)).1⟩
end ReciprocityTheory.AnForm.A.PshMean
