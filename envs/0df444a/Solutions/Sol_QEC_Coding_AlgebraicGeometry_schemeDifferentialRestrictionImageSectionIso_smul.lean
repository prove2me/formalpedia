-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:06:13.986649+00:00
-- url     : https://prove2.me/submissions/d020ce04-b562-4beb-88b3-1437a5faf48f

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
theorem _root_.solution (U : Y.Opens)
    (a : Γ(Y, U)) (s : Γ(OmegaY, U)) :
    (schemeDifferentialRestrictionImageSectionIso f k c U).hom (a • s) =
      (f.appIso U).inv a • (schemeDifferentialRestrictionImageSectionIso f k c U).hom s := by
  exact Scheme.Modules.Hom.app_smul (schemeDifferentialRestrictionIso f k c).hom a s
end QEC.Coding.AlgebraicGeometry
