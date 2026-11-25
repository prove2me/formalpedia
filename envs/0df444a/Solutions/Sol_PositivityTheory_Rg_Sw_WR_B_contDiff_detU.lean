-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_detU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:35.458573+00:00
-- url     : https://prove2.me/submissions/c1b49e62-577a-42b6-9020-0a3abcd7cf6a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_detAm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_detU_eq
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
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (uM s y).det) := by
  simp_rw [detU_eq]; exact (contDiff_detAm s).inv (det_Am_ne hs)
end PositivityTheory.Rg.Sw.WR.B
