-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_integralModel_weakDifferent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:04:31.144051+00:00
-- url     : https://prove2.me/submissions/7378e5c8-3c4d-489e-8c04-53a46c62d6ab

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementEndpoints
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AmbientPlaceModels_prime_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_restrictScalars_of_common_ambient_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_integralClosure_weakDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_restrictScalars_of_common_ambient_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_normalizedRefinement


set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.closureDifferent_modelDedekind
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.closureDifferent_modelFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.closureDifferent_modelFraction
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.closureDifferent_modelTorsionFree
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m))) :
    multiplicity Q.asIdeal (differentIdeal A (integralClosure A (SourceGaloisClosureField m))) =
      2 * ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal - 1) := by
  let E := SourceGaloisClosureField m
  let W := sourceClosureWBase m
  let R := heightOnePlace (k := F256) (K := E) Q
  let B := AmbientPlaceModels.baseRing W R
  let QB := AmbientPlaceModels.prime W R
  have hupper : (heightOnePlace (k := F256) (K := E) Q).order =
      (heightOnePlace (k := F256) (K := E) QB).order :=
    (AmbientPlaceModels.prime_order W R).symm
  have h := NormalizedRefinement.restrictScalars_of_common_ambient_order
    A B W W E Q QB hupper (sourceClosureW_normalizedRefinement m R)
  change NormalizedRefinement A W E Q ⊥ ⊤ at h
  exact NormalizedRefinement.integralClosure_weakDifferent A W E Q h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
