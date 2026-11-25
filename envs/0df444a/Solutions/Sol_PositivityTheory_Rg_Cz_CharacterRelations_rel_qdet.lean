-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.rel_qdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:58.092863+00:00
-- url     : https://prove2.me/submissions/eb83c2a6-1dc0-49fc-b05a-abbea247df0b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_add
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_alg
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_zero
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_intCast
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_sum
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_prod
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
variable {V N : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup N] [Module ℂ N]
  (W : Submodule ℂ V) (q : W →ₗ[ℂ] N)
variable {W q}
variable {n : ℕ}
namespace PositivityTheory.Rg.Cz.CharacterRelations
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ N)
    (h : ∀ a b, Rel W q (E a b) (F a b)) (u : ℂ) : Rel W q (qdet E u) (qdet F u) := by
  simp only [qdet, qminor]
  refine rel_sum _ _ _ fun σ => rel_mul (rel_intCast _) (rel_prod _ _ fun k => ?_)
  unfold Tm
  refine rel_add ?_ (h _ _)
  split_ifs
  · exact rel_alg _
  · exact rel_zero
end PositivityTheory.Rg.Cz.CharacterRelations
