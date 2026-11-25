-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.om_comm_xJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:19.723832+00:00
-- url     : https://prove2.me/submissions/5674de81-ec98-4fc9-bb46-01af5967f3b1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_comm_xJ
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
theorem _root_.solution (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (h : i < j) : Commute (Om E i) (xJ E j) :=
  comm_xJ E j _ (fun a b => (hT n M (Fin m) E hE _).2.1 i (by simpa using h) a b)
    (fun a b => (hT n M (Fin m) E hE _).2.1 i (by simp [h]) a b)
end PositivityTheory.Rg.Cz.JMA
