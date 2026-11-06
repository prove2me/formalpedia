-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionOver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:12:58.975161+00:00
-- url     : https://prove2.me/submissions/373f0a42-efc0-40c3-ab50-fd9853681e15

import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ChartBaseChange
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C]
variable {P U V X Z T : C}
variable (a : P ⟶ U) (b : P ⟶ V) (i : U ⟶ X) (j : V ⟶ X)
variable (x : X ⟶ Z) (t : T ⟶ Z)
namespace QEC.Coding.AlgebraicGeometry.ChartBaseChange
theorem _root_.solution (h : IsPullback a b i j) :
    IsPullback (firstOverlapOver a i x) (secondOverlapOver a b i j x h)
      (leftChartOver i x) (rightChartOver j x) := by
  apply IsPullback.of_map (Over.forget Z)
  · ext
    exact h.w
  · exact h
end QEC.Coding.AlgebraicGeometry.ChartBaseChange
