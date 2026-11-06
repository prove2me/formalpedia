-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ChartBaseChange.scalarFirstBaseChangedMap_scalarProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:00.227145+00:00
-- url     : https://prove2.me/submissions/2f6504e6-cb8f-41f2-abc4-372dc4f27747

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
    scalarFirstBaseChangedMap t f g u hu ≫ pullback.fst t g = pullback.fst t f := by
  simp only [scalarFirstBaseChangedMap, Category.assoc, pullbackSymmetry_inv_comp_fst,
    Over.pullback_map_left, Over.mk_hom, Over.homMk_left, pullback.lift_snd, pullbackSymmetry_hom_comp_snd]
end QEC.Coding.AlgebraicGeometry.ChartBaseChange
