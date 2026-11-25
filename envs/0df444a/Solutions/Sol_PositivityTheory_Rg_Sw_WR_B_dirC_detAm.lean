-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_detAm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:54.742901+00:00
-- url     : https://prove2.me/submissions/76927f92-df97-4bbc-9d65-71873db401ad

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_fderiv_detAm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_trace_comboN
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_uM_eq


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
    dirC (fun y => (Am s y).det) (vkl k l) y = -(Complex.I * s) * (Am s y).det * uM s y k l := by
  rw [dirC, fderiv_detAm hs, fderiv_detAm hs, ← uM_eq]
  linear_combination (Am s y).det * trace_comboN (uM s y) (Complex.I * s) k l
end PositivityTheory.Rg.Sw.WR.B
