-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeDifferentialRestrictionIso_derivation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:03:06.561741+00:00
-- url     : https://prove2.me/submissions/68fba2a3-f9cc-44b6-a472-ac4cbd267e7f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerRingIso
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialSheafDerivation_postcomp


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution :
    (schemeDifferentialSheafDerivation Y k (schemeRestrictionConstantMap f k c)).postcomp
      ((Scheme.Modules.toPresheafOfModules Y).map (schemeDifferentialRestrictionIso f k c).hom) =
    schemeRestrictedDifferentialSheafDerivation f k c := by
  rw [schemeDifferentialSheafDerivation_postcomp]
  exact (schemeDifferentialSheafHomEquiv Y k (schemeRestrictionConstantMap f k c)
    (schemeRestrictedDifferentialSheaf f k c)).apply_symm_apply
      (schemeRestrictedDifferentialSheafDerivation f k c)
end QEC.Coding.AlgebraicGeometry
