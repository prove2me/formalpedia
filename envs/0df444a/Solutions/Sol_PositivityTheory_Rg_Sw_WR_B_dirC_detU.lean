-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_detU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:29.361378+00:00
-- url     : https://prove2.me/submissions/c15a8d75-2b98-44b0-abf0-75c41a40007c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_detAm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_detAm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_detU_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_Am_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_diffAt_of
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_comp


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
    dirC (fun y => (uM s y).det) (vkl k l) y = Complex.I * s * uM s y k l * (uM s y).det := by
  simp_rw [detU_eq]
  rw [dirC_comp (hasDerivAt_inv (det_Am_ne hs y)) (diffAt_of (contDiff_detAm s) y), dirC_detAm hs]
  have := det_Am_ne hs y
  field_simp <;> ring
end PositivityTheory.Rg.Sw.WR.B
