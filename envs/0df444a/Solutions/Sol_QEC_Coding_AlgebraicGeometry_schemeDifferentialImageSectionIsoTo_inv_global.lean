-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialImageSectionIsoTo_inv_global
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:11:25.908211+00:00
-- url     : https://prove2.me/submissions/9af2d903-931f-4197-8c47-4878c628c39a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
    (h : schemeRestrictionConstantMap f k c = d)
    (s : Γ(schemeDifferentialSheaf X k c, ⊤)) :
    (schemeDifferentialRestrictionImageSectionIsoTo f k c d h ⊤).inv
      ((schemeDifferentialSheaf X k c).presheaf.map
        (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op s) =
    schemeDifferentialGlobalRestrictionTo f k c d h s := by
  subst d
  rfl
end QEC.Coding.AlgebraicGeometry
