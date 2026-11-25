-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.xJ_comm_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:35:18.43191+00:00
-- url     : https://prove2.me/submissions/09348ede-0280-41f4-8049-15b717fbc73b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_swap_comm_xJ
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_om_comm_xJ

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
theorem _root_.solution (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (h : i < j) : Commute (xJ E i) (xJ E j) := by
  show Commute (Om E i + ∑ l ∈ Finset.univ.filter (· < i), pm (Equiv.swap l i)) (xJ E j)
  refine (om_comm_xJ hT hE i j h).add_left (Commute.sum_left _ _ _ fun l hl => ?_)
  have hl' : l < i := (Finset.mem_filter.1 hl).2
  exact swap_comm_xJ hT hE j l i (iff_of_true (hl'.trans h) h)
    (iff_of_true (Or.inr (hl'.trans h)) (Or.inr h))
end PositivityTheory.Rg.Cz.JMA
