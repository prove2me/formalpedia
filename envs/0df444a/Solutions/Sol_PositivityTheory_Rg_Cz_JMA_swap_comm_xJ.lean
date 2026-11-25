-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.swap_comm_xJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:27:11.539203+00:00
-- url     : https://prove2.me/submissions/32529639-e9ca-4fab-b43b-f95eecca7c20

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_comm_xJ
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_swap_pres
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.JMA
theorem _root_.solution (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (k i j : Fin m)
    (h1 : i < k ↔ j < k) (h2 : (i = k ∨ i < k) ↔ (j = k ∨ j < k)) :
    Commute (pm (Equiv.swap i j)) (xJ E k) :=
  comm_xJ E k _ (fun a b => (hT n M (Fin m) E hE _).2.2.1 _ (swap_pres _ i j (by simpa using h1)) a b)
    (fun a b => (hT n M (Fin m) E hE _).2.2.1 _ (swap_pres _ i j (by simpa using h2)) a b)
end PositivityTheory.Rg.Cz.JMA
