-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ChartBaseChange.scalarFirstBaseChangedMap_chartProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:02.667892+00:00
-- url     : https://prove2.me/submissions/72d69311-6c69-491c-a840-e072d47d4e78

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
variable [HasPullbacks C]
namespace QEC.Coding.AlgebraicGeometry.ChartBaseChange
theorem _root_.solution {A B : C}
    (f : A ⟶ Z) (g : B ⟶ Z) (u : A ⟶ B) (hu : u ≫ g = f) :
    scalarFirstBaseChangedMap t f g u hu ≫ pullback.snd t g = pullback.snd t f ≫ u := by
  simp only [scalarFirstBaseChangedMap, Category.assoc, pullbackSymmetry_inv_comp_snd,
    Over.pullback_map_left, Over.mk_hom, pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc,
    Over.homMk_left]
end QEC.Coding.AlgebraicGeometry.ChartBaseChange
