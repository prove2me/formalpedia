-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.xJ_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:42:23.409078+00:00
-- url     : https://prove2.me/submissions/f19ea782-63d1-4de1-88a7-add0ec0ab076

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_xJ_comm_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.JMA
theorem _root_.solution (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m) :
    Commute (xJ E i) (xJ E j) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact xJ_comm_lt hT hE i j h
  · exact Commute.refl _
  · exact (xJ_comm_lt hT hE j i h).symm
end PositivityTheory.Rg.Cz.JMA
