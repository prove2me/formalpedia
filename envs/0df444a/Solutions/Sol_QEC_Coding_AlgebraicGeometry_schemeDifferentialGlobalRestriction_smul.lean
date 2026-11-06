-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalRestriction_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:07:10.815611+00:00
-- url     : https://prove2.me/submissions/813b4369-1f19-4743-892a-32ce4af6e292

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_additiveSectionIso_hom_injective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIso_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeRestrictionGlobal_appIso_inv_appTop

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
theorem _root_.solution (a : Γ(X, ⊤)) (s : Γ(OmegaX, ⊤)) :
    schemeDifferentialGlobalRestriction f k c (a • s) =
      f.appTop a • schemeDifferentialGlobalRestriction f k c s := by
  let e := schemeDifferentialRestrictionImageSectionIso f k c ⊤
  let i : f ''ᵁ ⊤ ⟶ (⊤ : X.Opens) := homOfLE le_top
  let r := (OmegaX).presheaf.map i.op
  apply additiveSectionIso_hom_injective e
  change e.hom (e.inv (r (a • s))) = e.hom (f.appTop a • e.inv (r s))
  have h1 : e.hom (e.inv (r (a • s))) = r (a • s) := Iso.inv_hom_id_apply e _
  have h2 : r (a • s) = X.presheaf.map i.op a • r s :=
    Scheme.Modules.map_smul («M» := OmegaX) i a s
  have h3 : X.presheaf.map i.op a • r s = (f.appIso ⊤).inv (f.appTop a) • r s :=
    congrArg (fun b => b • r s) (schemeRestrictionGlobal_appIso_inv_appTop f a).symm
  have h4 : (f.appIso ⊤).inv (f.appTop a) • r s =
      (f.appIso ⊤).inv (f.appTop a) • e.hom (e.inv (r s)) :=
    congrArg (fun z => (f.appIso ⊤).inv (f.appTop a) • z) (Iso.inv_hom_id_apply e (r s)).symm
  have h5 : (f.appIso ⊤).inv (f.appTop a) • e.hom (e.inv (r s)) =
      e.hom (f.appTop a • e.inv (r s)) :=
    (schemeDifferentialRestrictionImageSectionIso_smul f k c ⊤ (f.appTop a) (e.inv (r s))).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
end QEC.Coding.AlgebraicGeometry
