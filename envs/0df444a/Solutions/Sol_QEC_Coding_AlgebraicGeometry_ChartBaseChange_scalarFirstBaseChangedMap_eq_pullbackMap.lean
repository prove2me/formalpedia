-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ChartBaseChange.scalarFirstBaseChangedMap_eq_pullbackMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:58.940042+00:00
-- url     : https://prove2.me/submissions/e8a6bb58-84c2-40a7-b952-61f04165ddb6

import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_scalarFirstBaseChangedMap_scalarProjection
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_scalarFirstBaseChangedMap_chartProjection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ChartBaseChange
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B Z T : C} (t : T ⟶ Z)
namespace QEC.Coding.AlgebraicGeometry.ChartBaseChange
theorem _root_.solution
    (f : A ⟶ Z) (g : B ⟶ Z) (u : A ⟶ B) (hu : u ≫ g = f) :
    scalarFirstBaseChangedMap t f g u hu =
      pullback.map t f t g (𝟙 T) u (𝟙 Z) (by simp)
        (by simpa only [Category.comp_id] using hu.symm) := by
  apply pullback.hom_ext
  · simp only [scalarFirstBaseChangedMap_scalarProjection, pullback.map, pullback.lift_fst,
      Category.comp_id]
  · simp only [scalarFirstBaseChangedMap_chartProjection, pullback.map, pullback.lift_snd]
end QEC.Coding.AlgebraicGeometry.ChartBaseChange
