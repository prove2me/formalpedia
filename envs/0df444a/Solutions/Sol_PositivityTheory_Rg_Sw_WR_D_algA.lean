-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.algA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:27.747625+00:00
-- url     : https://prove2.me/submissions/14e04d2d-5170-49ee-91b2-f28009ca193b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_gramX_star
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_herm_hinv
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_WR_D_hinv_herm__6df79ca13e18
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_trace_herm_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_evX_detQ
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_qX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution : AlgA := by
  intro m n ε
  refine ⟨fun y x => ?_, fun x => herm_hinv _ (gramX_star ε x), hinv_herm', evX_detQ ε, continuous_qX ε⟩
  have h := trace_herm_mul y (qX ε x)
  rwa [show herm (qX ε x) = gramX ε x from herm_hinv _ (gramX_star ε x)] at h
end PositivityTheory.Rg.Sw.WR.D
