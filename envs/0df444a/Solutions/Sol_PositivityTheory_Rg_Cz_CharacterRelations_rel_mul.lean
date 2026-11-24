-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.rel_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:47.217551+00:00
-- url     : https://prove2.me/submissions/109773b5-7cab-407a-9de3-99b1512fe31c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar

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
namespace PositivityTheory.Rg.Cz.CharacterRelations
theorem _root_.solution {X X' Y Y'} (h : Rel W q X Y) (h' : Rel W q X' Y') : Rel W q (X * X') (Y * Y') := by
  intro w
  obtain ⟨h2, e2⟩ := h' w
  obtain ⟨h1, e1⟩ := h ⟨X' w, h2⟩
  exact ⟨h1, e1.trans (congrArg Y e2)⟩
end PositivityTheory.Rg.Cz.CharacterRelations
