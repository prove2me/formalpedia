-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.pm_swap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:49.660397+00:00
-- url     : https://prove2.me/submissions/6d8c06eb-8457-45e8-bf97-7973a135f1ec

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_comp_swap
import Theorems.Thm_PositivityTheory_Rg_Cz_eAt_apply
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
theorem _root_.solution {P : Type} [DecidableEq P] (p j : P) (h : p ≠ j) :
    (pm (Equiv.swap p j) : Module.End ℂ (TV n M P)) = ∑ a, ∑ b, eAt p a b * eAt j b a := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [pm_apply, comp_swap I p j h]
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, eAt_apply,
    Function.update_apply, if_neg (Ne.symm h)]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
end PositivityTheory.Rg.Cz.JMA
