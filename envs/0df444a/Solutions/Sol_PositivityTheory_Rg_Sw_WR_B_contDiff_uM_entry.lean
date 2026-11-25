-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_uM_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:54.713553+00:00
-- url     : https://prove2.me/submissions/91a86811-14d8-4c7e-b6cb-8990001408e0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_inv_entry_of
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_Am_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_Am_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (a b : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => uM s y a b) :=
  contDiff_inv_entry_of (contDiff_Am_entry s) (det_Am_ne hs) a b
end PositivityTheory.Rg.Sw.WR.B
