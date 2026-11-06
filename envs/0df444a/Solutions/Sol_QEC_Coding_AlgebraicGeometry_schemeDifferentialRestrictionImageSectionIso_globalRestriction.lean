-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionImageSectionIso_globalRestriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:11:19.328574+00:00
-- url     : https://prove2.me/submissions/24a3fa70-c411-4eaa-aea9-cbb1d0919768

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIso_comp
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIso_naturality

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
theorem _root_.solution
    (s : Γ(OmegaY, ⊤)) :
    (schemeDifferentialRestrictionImageSectionIsoTo (g ≫ f) k c cZ
      (schemeRestrictionConstantMap_comp f g k c) ⊤).hom
        (schemeDifferentialGlobalRestriction g k cY s) =
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image g f ⊤)).op
      ((OmegaX).presheaf.map
        (f.opensFunctor.map (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤)).op
          ((schemeDifferentialRestrictionImageSectionIso f k c ⊤).hom s)) := by
  have hc := schemeDifferentialRestrictionImageSectionIso_comp f g k c ⊤
    (schemeDifferentialGlobalRestriction g k cY s)
  have hi : (schemeDifferentialRestrictionImageSectionIso g k cY ⊤).hom
      (schemeDifferentialGlobalRestriction g k cY s) =
    (OmegaY).presheaf.map (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤).op s :=
    Iso.inv_hom_id_apply (schemeDifferentialRestrictionImageSectionIso g k cY ⊤) _
  have hn := schemeDifferentialRestrictionImageSectionIso_naturality f k c
    (homOfLE le_top : g ''ᵁ ⊤ ⟶ ⊤) s
  exact hc.trans (congrArg (fun z : Γ(OmegaX, f ''ᵁ (g ''ᵁ ⊤)) =>
    (OmegaX).presheaf.map (eqToHom (Scheme.Hom.comp_image g f ⊤)).op z)
      ((congrArg (fun z : Γ(OmegaY, g ''ᵁ ⊤) =>
        (schemeDifferentialRestrictionImageSectionIso f k c (g ''ᵁ ⊤)).hom z) hi).trans hn))
end QEC.Coding.AlgebraicGeometry
