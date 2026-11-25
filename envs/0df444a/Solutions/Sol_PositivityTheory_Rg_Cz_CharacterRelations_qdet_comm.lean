-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.qdet_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:14.254927+00:00
-- url     : https://prove2.me/submissions/7df74b84-1038-4799-a5f4-037ad78f136a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_comm_alg
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
open Formalism.REAL Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.CharacterRelations
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CharacterRelations
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] (T : A) (E : Fin n → Fin n → A)
    (h : ∀ a b, Commute T (E a b)) (u : ℂ) : Commute T (qdet E u) := by
  simp only [qdet, qminor]
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine Commute.mul_right Commute.intCast_right (Commute.list_prod_right _ _ ?_)
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  unfold Tm
  refine Commute.add_right ?_ (h _ _)
  split_ifs
  · exact comm_alg _ _
  · exact Commute.zero_right _
end PositivityTheory.Rg.Cz.CharacterRelations
