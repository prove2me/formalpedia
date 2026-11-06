-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalRestrictionTo_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:08:26.242925+00:00
-- url     : https://prove2.me/submissions/b9f869cd-af85-4794-acda-762c8286359d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialGlobalRestriction_smul

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
variable (h : schemeRestrictionConstantMap f k c = d)
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k d
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (a : Γ(X, ⊤)) (s : Γ(OmegaX, ⊤)) :
    schemeDifferentialGlobalRestrictionTo f k c d h (a • s) =
      f.appTop a • schemeDifferentialGlobalRestrictionTo f k c d h s := by
  subst d
  exact schemeDifferentialGlobalRestriction_smul f k c a s
end QEC.Coding.AlgebraicGeometry
