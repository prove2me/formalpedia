-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialGlobalRestrictionTo_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:09:10.787244+00:00
-- url     : https://prove2.me/submissions/6afdd004-ab56-45c4-bb5e-908e4bf6e8a6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialGlobalRestriction_D

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
theorem _root_.solution (a : Γ(X, ⊤)) :
    schemeDifferentialGlobalRestrictionTo f k c d h
      ((schemeDifferentialSheafDerivation X k c).d (X := op ⊤) a) =
      (schemeDifferentialSheafDerivation Y k d).d (X := op ⊤) (f.appTop a) := by
  subst d
  exact schemeDifferentialGlobalRestriction_D f k c a
end QEC.Coding.AlgebraicGeometry
