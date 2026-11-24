-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_push_zero__4bd36dbeb085
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:40.718541+00:00
-- url     : https://prove2.me/submissions/79e355c1-aa2e-4c47-a7fd-e05c35f1720d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable {P}
attribute [local semireducible] inter

namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (n : ℕ) (σ : Cochain P U n) :
    push U (0 : P ⟶ P') n σ = 0 := by
  funext i
  simp [push]
end GroundTheory.Arith.SchemeCoh
