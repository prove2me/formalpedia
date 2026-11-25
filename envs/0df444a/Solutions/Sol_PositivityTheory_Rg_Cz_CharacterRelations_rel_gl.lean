-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.rel_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:32.281653+00:00
-- url     : https://prove2.me/submissions/531ca32c-7be8-40fd-be6e-70287ffaf92b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_sub
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_zero
import Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_rel_uniq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hq : Function.Surjective q) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ N)
    (hE : GlRel E) (h : ∀ a b, Rel W q (E a b) (F a b)) : GlRel F := by
  intro a b c d
  have h1 := rel_sub (rel_mul (h a b) (h c d)) (rel_mul (h c d) (h a b))
  rw [hE a b c d] at h1
  have h2 : Rel W q ((if b = c then E a d else 0) - if d = a then E c b else 0)
      ((if b = c then F a d else 0) - if d = a then F c b else 0) := by
    refine rel_sub ?_ ?_
    · split_ifs
      · exact h _ _
      · exact rel_zero
    · split_ifs
      · exact h _ _
      · exact rel_zero
  exact rel_uniq hq h1 h2
end PositivityTheory.Rg.Cz.CharacterRelations
