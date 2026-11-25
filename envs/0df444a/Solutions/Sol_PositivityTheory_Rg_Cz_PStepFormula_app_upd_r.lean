-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.app_upd_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:36:25.254804+00:00
-- url     : https://prove2.me/submissions/d50a221f-a5cd-441a-b7ff-11d36ced867c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
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
open PositivityTheory.Rg.Cz.PStepFormula
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.PStepFormula
theorem _root_.solution {α : Type} {m k : ℕ} (I : Fin m → α) (J : Fin k → α) (j : Fin k) (a : α) :
    Function.update (Fin.append I J) (Fin.natAdd m j) a = Fin.append I (Function.update J j a) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · rw [Fin.append_left, Function.update_of_ne, Fin.append_left]
    intro h; have := congrArg Fin.val h; simp at this; omega
  · by_cases h : i = j
    · subst h; simp
    · rw [Function.update_of_ne, Fin.append_right, Fin.append_right, Function.update_of_ne h]
      intro h'; exact h (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))
end PositivityTheory.Rg.Cz.PStepFormula
