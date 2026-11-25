-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMean.smul_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:08.826348+00:00
-- url     : https://prove2.me/submissions/a77ba8a6-7501-4e1f-b8eb-f7c109da7913

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_mul_mp

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
theorem _root_.solution (c : ℂ) (hc : ‖c‖ = 1) :
    MeasurePreserving (fun v : Fin D → ℂ => c • v) volume volume :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun _ => mul_mp c hc)
end ReciprocityTheory.AnForm.A.PshMean
