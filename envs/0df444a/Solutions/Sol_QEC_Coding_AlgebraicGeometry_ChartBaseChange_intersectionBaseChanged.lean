-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionBaseChanged
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:14:17.824208+00:00
-- url     : https://prove2.me/submissions/c849bc83-5862-4814-807a-2063bcbf04dd

import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_intersectionBaseChangedOver

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ChartBaseChange
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C]
variable {P U V X Z T : C}
variable (a : P ⟶ U) (b : P ⟶ V) (i : U ⟶ X) (j : V ⟶ X)
variable (x : X ⟶ Z) (t : T ⟶ Z)
variable [HasPullbacks C]
namespace QEC.Coding.AlgebraicGeometry.ChartBaseChange
theorem _root_.solution (h : IsPullback a b i j) :
    IsPullback (((Over.pullback t).map (firstOverlapOver a i x)).left)
      (((Over.pullback t).map (secondOverlapOver a b i j x h)).left)
      (((Over.pullback t).map (leftChartOver i x)).left)
      (((Over.pullback t).map (rightChartOver j x)).left) :=
  (intersectionBaseChangedOver a b i j x t h).map (Over.forget T)
end QEC.Coding.AlgebraicGeometry.ChartBaseChange
