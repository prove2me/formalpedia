-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.rel_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:38.197874+00:00
-- url     : https://prove2.me/submissions/bbc0f062-6a1d-4965-959e-433df4b7dc9f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_add
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_zero
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
namespace PositivityTheory.Rg.Cz.CharacterRelations
theorem _root_.solution {ι : Type*} (s : Finset ι) (X : ι → Module.End ℂ V) (Y : ι → Module.End ℂ N)
    (h : ∀ i, Rel W q (X i) (Y i)) : Rel W q (∑ i ∈ s, X i) (∑ i ∈ s, Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha]; exact rel_add (h a) ih
end PositivityTheory.Rg.Cz.CharacterRelations
