-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_integralModel_differentialGeneratorOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:04:31.95109+00:00
-- url     : https://prove2.me/submissions/1bd79471-c8d2-4521-ba4b-2e7da58bd6f3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedDifferentialRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AmbientPlaceModels_prime_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_restrictScalars_of_common_ambient_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_integralClosure_differentialGeneratorOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_restrictScalars_of_common_ambient_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_normalizedRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero


set_option autoImplicit false
open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m))) :
    differentialOrder (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q)
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero =
    ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) *
      differentialOrder (heightOnePlace (k := F256) (K := sourceClosureWBase m) (Q.under A))
        (functionFieldDifferentialGenerator (k := F256) (F := sourceClosureWBase m))
        functionFieldDifferentialGenerator_ne_zero +
      2 * (((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) - 1) := by
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
  exact NormalizedRefinement.integralClosure_differentialGeneratorOrder A W E Q h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
