-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_detV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:38:53.461588+00:00
-- url     : https://prove2.me/submissions/e6d33e0c-8116-46be-8868-fab0e95db11e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_detBm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_detV_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_Bm_ne


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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (vM s y).det) := by
  simp_rw [detV_eq]; exact (contDiff_detBm s).inv (det_Bm_ne hs)
end PositivityTheory.Rg.Sw.WR.B
