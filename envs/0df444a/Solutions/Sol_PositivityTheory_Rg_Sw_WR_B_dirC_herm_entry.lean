-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_herm_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:58.23562+00:00
-- url     : https://prove2.me/submissions/2912c70f-406a-4171-965e-6c661e3af50c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_of
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_hc_vkl
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_hermE_apply

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
theorem _root_.solution (a b k l : Fin n) (y : E n) :
    dirC (fun y => herm y a b) (vkl k l) y = Matrix.single l k 1 a b := by
  rw [show (fun y => herm y a b) = hermE a b from rfl, dirC_of (hermE a b).hasFDerivAt, hermE_apply, hermE_apply,
    ← hc_vkl k l]
  simp [Matrix.add_apply, Matrix.smul_apply]
end PositivityTheory.Rg.Sw.WR.B
