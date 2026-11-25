-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.app_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:34:05.625994+00:00
-- url     : https://prove2.me/submissions/d80e9609-7e1d-46d4-ad29-c45f804840b2

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
theorem _root_.solution (I : Fin 1 → Fin n) (J : Fin n → Fin n) (j : Fin n) :
    Fin.append I J ∘ Equiv.swap (Fin.natAdd 1 j) (Fin.castAdd n 0) =
      Fin.append (Function.update I 0 (J j)) (Function.update J j (I 0)) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [Equiv.swap_apply_right, Fin.append_left, Fin.append_right]
  · by_cases h : i = j
    · subst h; simp [Fin.append_left, Fin.append_right]
    · have h1 : Fin.natAdd 1 i ≠ Fin.natAdd 1 j := fun h' => h (Fin.ext (by
        have := congrArg Fin.val h'; simp at this; omega))
      have h2 : Fin.natAdd 1 i ≠ Fin.castAdd n 0 := fun h' => by
        have := congrArg Fin.val h'; simp at this
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right, Fin.append_right,
        Function.update_of_ne h]
end PositivityTheory.Rg.Cz.PStepFormula
