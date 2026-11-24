-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CharacterRelations.rel_uniq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:51.094137+00:00
-- url     : https://prove2.me/submissions/a75ff9b8-1440-435e-8ee6-bb8bee366d59

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
theorem _root_.solution (hq : Function.Surjective q) {X Y Y'} (h : Rel W q X Y) (h' : Rel W q X Y') : Y = Y' := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨w, rfl⟩ := hq y
  obtain ⟨h1, e1⟩ := h w
  obtain ⟨h2, e2⟩ := h' w
  rw [← e1, ← e2]
end PositivityTheory.Rg.Cz.CharacterRelations
