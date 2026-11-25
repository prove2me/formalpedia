-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_detV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:58.658012+00:00
-- url     : https://prove2.me/submissions/707ee7af-4f0d-4cae-9ec8-04a7e0bfda44

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_detBm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_detBm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_detV_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_Bm_ne
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
    dirC (fun y => (vM s y).det) (vkl k l) y = -(Complex.I * s * vM s y k l * (vM s y).det) := by
  simp_rw [detV_eq]
  rw [dirC_comp (hasDerivAt_inv (det_Bm_ne hs y)) (diffAt_of (contDiff_detBm s) y), dirC_detBm hs]
  have := det_Bm_ne hs y
  field_simp <;> ring
end PositivityTheory.Rg.Sw.WR.B
