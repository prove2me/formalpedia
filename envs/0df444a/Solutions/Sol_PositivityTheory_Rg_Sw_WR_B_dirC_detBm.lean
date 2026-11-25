-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_detBm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:51:25.603065+00:00
-- url     : https://prove2.me/submissions/9629c965-625f-4f66-8115-5dbd06402f45

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_fderiv_detBm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_trace_combo
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_vM_eq


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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (k l : Fin n) :
    dirC (fun y => (Bm s y).det) (vkl k l) y = Complex.I * s * (Bm s y).det * vM s y k l := by
  rw [dirC, fderiv_detBm hs, fderiv_detBm hs, ← vM_eq]
  linear_combination (Bm s y).det * trace_combo (vM s y) (Complex.I * s) k l
end PositivityTheory.Rg.Sw.WR.B
