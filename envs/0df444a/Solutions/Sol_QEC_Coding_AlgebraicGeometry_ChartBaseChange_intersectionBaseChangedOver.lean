-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionBaseChangedOver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:32.514256+00:00
-- url     : https://prove2.me/submissions/b2aeaef3-c03f-445d-ab6e-27dcbdcb5adf

import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_intersectionOver

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
    IsPullback ((Over.pullback t).map (firstOverlapOver a i x))
      ((Over.pullback t).map (secondOverlapOver a b i j x h))
      ((Over.pullback t).map (leftChartOver i x))
      ((Over.pullback t).map (rightChartOver j x)) :=
  (intersectionOver a b i j x h).map (Over.pullback t)
end QEC.Coding.AlgebraicGeometry.ChartBaseChange
