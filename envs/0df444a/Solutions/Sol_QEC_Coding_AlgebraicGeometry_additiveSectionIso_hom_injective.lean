-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.additiveSectionIso_hom_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:04:12.994381+00:00
-- url     : https://prove2.me/submissions/e8f32961-27ad-4ad3-8e61-42b1afcc1e48

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k (schemeRestrictionConstantMap f k c)
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution {A B : AddCommGrpCat.{u}} (e : A ≅ B) :
    Function.Injective e.hom := by
  intro a b h
  have hh := congrArg (fun x : B => e.inv x) h
  exact (Iso.hom_inv_id_apply e a).symm.trans (hh.trans (Iso.hom_inv_id_apply e b))
end QEC.Coding.AlgebraicGeometry
