-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIsoTo_globalRestriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:12:30.575232+00:00
-- url     : https://prove2.me/submissions/b36a7cd1-fdc4-4bd2-ae74-1a4838508376

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIso_globalRestriction

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
variable (d : k ⟶ Γ(Y, ⊤)) (e : k ⟶ Γ(Z, ⊤))
variable (hf : schemeRestrictionConstantMap f k c = d)
variable (hg : schemeRestrictionConstantMap g k d = e)
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (s : Γ(schemeDifferentialSheaf Y k d, ⊤)) :
    (schemeDifferentialRestrictionImageSectionIsoTo (g ≫ f) k c e
      (schemeRestrictionConstantMap_comp_to f g k c d e hf hg) ⊤).hom
        (schemeDifferentialGlobalRestrictionTo g k d e hg s) =
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image g f ⊤)).op
      ((OmegaX).presheaf.map
        (f.opensFunctor.map (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤)).op
          ((schemeDifferentialRestrictionImageSectionIsoTo f k c d hf ⊤).hom s)) := by
  subst d
  subst e
  exact schemeDifferentialRestrictionImageSectionIso_globalRestriction f g k c s
end QEC.Coding.AlgebraicGeometry
