-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:05:18.480473+00:00
-- url     : https://prove2.me/submissions/70229d15-a3f6-4919-89cb-b1e4bbda5ea8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionIso_derivation


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
theorem _root_.solution (U : Y.Opens) (a : Γ(Y, U)) :
    (schemeDifferentialRestrictionImageSectionIso f k c U).hom
      ((schemeDifferentialSheafDerivation Y k (schemeRestrictionConstantMap f k c)).d
        (X := op U) a) =
    (schemeDifferentialSheafDerivation X k c).d (X := op (f ''ᵁ U))
      ((f.appIso U).inv a) := by
  exact PresheafOfModules.Derivation.congr_d
    (schemeDifferentialRestrictionIso_derivation f k c) (X := op U) a
end QEC.Coding.AlgebraicGeometry
