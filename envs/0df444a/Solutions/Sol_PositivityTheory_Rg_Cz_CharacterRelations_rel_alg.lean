-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.rel_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:33.715191+00:00
-- url     : https://prove2.me/submissions/de2529aa-086c-42d2-9272-075bcf5b7812

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
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
theorem _root_.solution (c : ℂ) : Rel W q (algebraMap ℂ _ c) (algebraMap ℂ _ c) := by
  intro w
  refine ⟨by rw [Module.algebraMap_end_apply]; exact W.smul_mem c w.2, ?_⟩
  have e : (⟨algebraMap ℂ (Module.End ℂ V) c w, by rw [Module.algebraMap_end_apply]; exact W.smul_mem c w.2⟩ : W) = c • w :=
    Subtype.ext (by simp [Module.algebraMap_end_apply])
  rw [e, map_smul, Module.algebraMap_end_apply]
end PositivityTheory.Rg.Cz.CharacterRelations
