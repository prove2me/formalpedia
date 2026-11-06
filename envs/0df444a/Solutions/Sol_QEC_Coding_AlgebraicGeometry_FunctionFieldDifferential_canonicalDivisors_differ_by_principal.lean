-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.canonicalDivisors_differ_by_principal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:29:57.740364+00:00
-- url     : https://prove2.me/submissions/ecd0bc39-ca64-4f8a-b2dd-9eb3c6d053a3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
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
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution
    [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    {K L : Divisor (GlobalPlace k F)}
    (hK : IsCanonicalDivisor (k := k) (F := F) K)
    (hL : IsCanonicalDivisor (k := k) (F := F) L) :
    ∃ u : Fˣ, L = GlobalPlace.principalDivisor (k := k) (F := F) u + K := by
  rcases hK with ⟨omega, homega, rfl⟩
  rcases hL with ⟨eta, heta, rfl⟩
  have homega_coordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff (k := k) (F := F) omega).mpr homega
  have heta_coordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F) eta ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff (k := k) (F := F) eta).mpr heta
  let u : Fˣ := Units.mk0
    (functionFieldDifferentialCoordinate (k := k) (F := F) eta /
      functionFieldDifferentialCoordinate (k := k) (F := F) omega)
    (div_ne_zero heta_coordinate homega_coordinate)
  refine ⟨u, ?_⟩
  have hscalar : (u : F) • omega = eta := by
    apply (functionFieldDifferentialEquiv (k := k) (F := F)).injective
    change functionFieldDifferentialCoordinate (k := k) (F := F) ((u : F) • omega) =
      functionFieldDifferentialCoordinate (k := k) (F := F) eta
    simp only [map_smul, smul_eq_mul, u, Units.val_mk0]
    exact div_mul_cancel₀ _ homega_coordinate
  simpa only [hscalar] using
    (differentialDivisor_smul (k := k) (F := F) u omega homega)
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
