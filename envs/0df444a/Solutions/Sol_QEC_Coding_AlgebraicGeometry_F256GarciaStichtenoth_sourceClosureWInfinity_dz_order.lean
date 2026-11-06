-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWInfinity_dz_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:39:34.425405+00:00
-- url     : https://prove2.me/submissions/accd72a1-7ce9-48d8-bf91-3c4e6e8d43c1

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_WBaseDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureWBase_dz_order_infinity_fibre
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_integralModel_differentialGeneratorOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureInfinityPlace_order_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityRamificationIndex_eq_prime
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_eq_of_order_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_heightOne_valuationRing_order


set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
  fibreDifferent_baseAlgebra fibreDifferent_baseFraction fibreDifferent_baseFaithful
  fibreDifferent_baseDVR fibreDifferent_ambientAlgebra fibreDifferent_baseTower
  fibreDifferent_ambientTorsionFree
set_option maxHeartbeats 1000000
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) (P : SourceGaloisWInfinityPrime m) :
    differentialOrder (sourceGaloisWInfinityPlaceOfPrime m P)
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero =
        -14 * (sourceGaloisWInfinityRamificationIndex m : ℤ) - 2 := by
  let B := sourceGaloisWClosureInfinityPlace m
  let A := B.valuationRing
  let Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)) :=
    sourceGaloisWInfinityUpperHeightOne m P
  have h := sourceClosureW_integralModel_differentialGeneratorOrder m A Q
  have hlow := differentialGenerator_order_eq_of_order_eq
    (heightOnePlace (k := F256) (K := sourceClosureWBase m) (Q.under A)) B
    (B.heightOne_valuationRing_order (Q.under A))
  have hb := sourceClosureWBase_dz_order_infinity_fibre m B
    (sourceGaloisWClosureInfinityPlace_order_generator m)
  have hp : (Q.under A).asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Q.under A).isMaximal
  rw [hlow, hb, hp] at h
  have he : (IsLocalRing.maximalIdeal A).ramificationIdx' Q.asIdeal =
      sourceGaloisWInfinityRamificationIndex m :=
    (sourceGaloisWInfinityRamificationIndex_eq_prime m P).symm
  rw [he] at h
  change differentialOrder (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q)
    functionFieldDifferentialGenerator functionFieldDifferentialGenerator_ne_zero = _
  rw [h]
  ring
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
