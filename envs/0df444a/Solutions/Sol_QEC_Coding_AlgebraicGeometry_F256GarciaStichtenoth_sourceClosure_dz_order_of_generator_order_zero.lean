-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosure_dz_order_of_generator_order_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:27:03.950225+00:00
-- url     : https://prove2.me/submissions/06f308c0-aad6-4789-b41a-a0ed57c91424

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureUnramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_WBaseDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_integralModel_dz_order_of_generator_order_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AmbientPlaceModels_prime_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_eq_of_order_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero


set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
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
    (Q : GlobalPlace F256 (SourceGaloisClosureField m))
    (hw : Q.order (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 0) :
    differentialOrder Q
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero = 0 := by
  let W := sourceClosureWBase m
  let B := AmbientPlaceModels.baseRing W Q
  let H := AmbientPlaceModels.prime W Q
  have ho := AmbientPlaceModels.prime_order W Q
  have hg := differentialGenerator_order_eq_of_order_eq
    (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) H) Q ho
  rw [← hg]
  apply sourceClosureW_integralModel_dz_order_of_generator_order_zero m B H
  change (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) H).order _ = 0
  rw [ho, hw]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
