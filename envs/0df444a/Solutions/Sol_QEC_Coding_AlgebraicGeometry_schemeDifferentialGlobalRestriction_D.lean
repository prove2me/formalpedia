-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalRestriction_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:07:26.364397+00:00
-- url     : https://prove2.me/submissions/48c7b1f0-5833-4677-a9db-22a43a01ce56

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_additiveSectionIso_hom_injective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionImageSectionIso_D

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
theorem _root_.solution (a : Γ(X, ⊤)) :
    schemeDifferentialGlobalRestriction f k c
      ((schemeDifferentialSheafDerivation X k c).d (X := op ⊤) a) =
    (schemeDifferentialSheafDerivation Y k (schemeRestrictionConstantMap f k c)).d
      (X := op ⊤) (f.appTop a) := by
  let e := schemeDifferentialRestrictionImageSectionIso f k c ⊤
  let r := (OmegaX).presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op
  apply additiveSectionIso_hom_injective e
  have he : e.hom (e.inv (r ((schemeDifferentialSheafDerivation X k c).d a))) =
      r ((schemeDifferentialSheafDerivation X k c).d a) := by
    exact Iso.inv_hom_id_apply e _
  change e.hom (e.inv (r ((schemeDifferentialSheafDerivation X k c).d a))) =
    e.hom ((schemeDifferentialSheafDerivation Y k (schemeRestrictionConstantMap f k c)).d
      (f.appTop a))
  rw [he]
  have hr : (f.appIso ⊤).inv (f.appTop a) =
      X.presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op a := by
    have htop : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
    have h := f.appLE_appIso_inv (U := ⊤) (V := ⊤) (by simp)
    rw [htop] at h
    exact congrArg (fun t => t a) h
  have hd := (schemeDifferentialSheafDerivation X k c).d_map
    (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op a
  exact hd.symm.trans ((congrArg
    (fun z => (schemeDifferentialSheafDerivation X k c).d (X := op (f ''ᵁ ⊤)) z)
      hr.symm).trans (schemeDifferentialRestrictionImageSectionIso_D f k c ⊤
        (f.appTop a)).symm)
end QEC.Coding.AlgebraicGeometry
