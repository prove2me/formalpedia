-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialGenerator_order_eq_of_order_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:18:08.179207+00:00
-- url     : https://prove2.me/submissions/c60b6a5d-2fa2-4184-84ea-83d8693def36

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralModelCentre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_of_order_one_or_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
attribute [local instance] QEC.Coding.AlgebraicGeometry.placeTransportDVR
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution (P Q : GlobalPlace k K)
    (horder : P.order = Q.order) :
    differentialOrder P (functionFieldDifferentialGenerator (k := k) (F := K))
      functionFieldDifferentialGenerator_ne_zero =
    differentialOrder Q (functionFieldDifferentialGenerator (k := k) (F := K))
      functionFieldDifferentialGenerator_ne_zero := by
  have ht : P.uniformizer ≠ 0 := by
    intro hz
    have h := P.order_uniformizer
    rw [hz] at h
    simp [GlobalPlace.order] at h
  have hQ : Q.order P.uniformizer = 1 := by rw [← horder, P.order_uniformizer]
  obtain ⟨_, hP⟩ := differentialGenerator_order_of_order_one_or_neg_one
    P P.uniformizer ht (.inl P.order_uniformizer)
  obtain ⟨_, hQ⟩ := differentialGenerator_order_of_order_one_or_neg_one
    Q P.uniformizer ht (.inl hQ)
  rw [hP, hQ, horder]
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
