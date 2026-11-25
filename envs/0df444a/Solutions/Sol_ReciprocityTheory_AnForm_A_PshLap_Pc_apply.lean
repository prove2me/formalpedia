-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.Pc_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:33.198026+00:00
-- url     : https://prove2.me/submissions/3c1d2411-43ff-4506-913d-e5e04b426298

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution (w : Fin D → ℂ) (T : (Fin D → ℂ) →L[ℝ] ℝ) (a : ℂ) : Pc w T a = T (a • w) := by
  simp [Pc, L0]
end ReciprocityTheory.AnForm.A.PshLap
