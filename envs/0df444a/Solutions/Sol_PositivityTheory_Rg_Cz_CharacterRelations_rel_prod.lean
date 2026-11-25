-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.rel_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:32.176364+00:00
-- url     : https://prove2.me/submissions/8ca85295-5bf5-453a-b326-03dcfcca757f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_alg
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
theorem _root_.solution {t : ℕ} (X : Fin t → Module.End ℂ V) (Y : Fin t → Module.End ℂ N)
    (h : ∀ i, Rel W q (X i) (Y i)) : Rel W q (List.ofFn X).prod (List.ofFn Y).prod := by
  induction t with
  | zero => simpa using rel_alg (W := W) (q := q) 1
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact rel_mul (h 0) (ih _ _ fun i => h i.succ)
end PositivityTheory.Rg.Cz.CharacterRelations
