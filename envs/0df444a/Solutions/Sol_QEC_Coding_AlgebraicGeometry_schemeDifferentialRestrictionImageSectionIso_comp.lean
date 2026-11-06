-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:10:16.082275+00:00
-- url     : https://prove2.me/submissions/acdbf878-8cb0-47e7-9d8d-385c6db8d2ac

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionComparison_comp

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "cY" => schemeRestrictionConstantMap f k c
local notation "cZ" => schemeRestrictionConstantMap g k cY
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k cY
local notation "OmegaZ" => schemeDifferentialSheaf Z k cZ
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (U : Z.Opens) (s : Γ(OmegaZ, U)) :
    (schemeDifferentialRestrictionImageSectionIsoTo (g ≫ f) k c cZ
      (schemeRestrictionConstantMap_comp f g k c) U).hom s =
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image g f U)).op
      ((schemeDifferentialRestrictionImageSectionIso f k c (g ''ᵁ U)).hom
        ((schemeDifferentialRestrictionImageSectionIso g k cY U).hom s)) := by
  have hc := congrArg (fun t : OmegaZ ⟶
      (Scheme.Modules.restrictFunctor (g ≫ f)).obj OmegaX => t.app U s)
    (schemeDifferentialRestrictionComparison_comp f g k c)
  exact hc
end QEC.Coding.AlgebraicGeometry
