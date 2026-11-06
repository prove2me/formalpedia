-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ChartBaseChange.intersectionBaseChangedScalarFirst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:56.73957+00:00
-- url     : https://prove2.me/submissions/18b29fa3-6f8e-42c0-850e-709dc20d8c93

import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_intersectionBaseChanged

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
    IsPullback
      (scalarFirstBaseChangedMap t (a ≫ i ≫ x) (i ≫ x) a rfl)
      (scalarFirstBaseChangedMap t (a ≫ i ≫ x) (j ≫ x) b
        (by simpa only [Category.assoc] using congrArg (fun k => k ≫ x) h.w.symm))
      (scalarFirstBaseChangedMap t (i ≫ x) x i rfl)
      (scalarFirstBaseChangedMap t (j ≫ x) x j rfl) := by
  apply (intersectionBaseChanged a b i j x t h).of_iso'
    (pullbackSymmetry t (a ≫ i ≫ x)) (pullbackSymmetry t (i ≫ x))
    (pullbackSymmetry t (j ≫ x)) (pullbackSymmetry t x)
  · simp [scalarFirstBaseChangedMap, firstOverlapOver, Category.assoc]
  · simp [scalarFirstBaseChangedMap, secondOverlapOver, Category.assoc]
  · simp [scalarFirstBaseChangedMap, leftChartOver, Category.assoc]
  · simp [scalarFirstBaseChangedMap, rightChartOver, Category.assoc]
end QEC.Coding.AlgebraicGeometry.ChartBaseChange
