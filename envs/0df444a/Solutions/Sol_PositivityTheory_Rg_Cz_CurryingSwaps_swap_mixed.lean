-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CurryingSwaps.swap_mixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:35.141125+00:00
-- url     : https://prove2.me/submissions/c74c9190-2c42-4d5f-921e-d7e763596787

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PCurry
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
open PositivityTheory.Rg.Cz.CurryingSwaps
variable {α : Type*} {m k : ℕ}
namespace PositivityTheory.Rg.Cz.CurryingSwaps
theorem _root_.solution (I : Fin m → α) (J : Fin k → α) (i : Fin m) (j : Fin k) :
    Fin.append I J ∘ Equiv.swap (Fin.castAdd k i) (Fin.natAdd m j) =
      Fin.append (Function.update I i (J j)) (Function.update J j (I i)) := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x
  · have h2 : Fin.castAdd k a ≠ Fin.natAdd m j := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : a = i
    · subst h; simp
    · have h1 : Fin.castAdd k a ≠ Fin.castAdd k i := fun e => h (Fin.castAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_left,
        Function.update_of_ne h]
  · have h1 : Fin.natAdd m b ≠ Fin.castAdd k i := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases h : b = j
    · subst h; simp
    · have h2 : Fin.natAdd m b ≠ Fin.natAdd m j := fun e => h (Fin.natAdd_injective _ _ e)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right,
        Function.update_of_ne h]
end PositivityTheory.Rg.Cz.CurryingSwaps
