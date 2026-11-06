-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeRestrictionGlobal_appIso_inv_appTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:06:19.117435+00:00
-- url     : https://prove2.me/submissions/f7618577-21cd-4f3c-a958-daacefefe5af

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
theorem _root_.solution (a : Γ(X, ⊤)) :
    (f.appIso ⊤).inv (f.appTop a) =
      X.presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op a := by
  have htop : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
  have h := f.appLE_appIso_inv (U := ⊤) (V := ⊤) (by simp)
  rw [htop] at h
  exact congrArg (fun t => t a) h
end QEC.Coding.AlgebraicGeometry
