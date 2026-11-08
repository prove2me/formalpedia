-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChart_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:12:13.458091+00:00
-- url     : https://prove2.me/submissions/618eb999-92a5-4df7-b544-2e56a61ac1ae

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerFiniteness

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary027
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary028
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary029
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary030
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary031
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary032
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary033
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary034
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary035
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary036
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary037
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary038
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary039
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary040
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary041
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary042
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary043
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : Algebra.FiniteType ℂ R := by
  let : Algebra P J := lpsOriginalReciprocalBaseCAlgebra
  let : SMul P J := Algebra.toSMul
  let : Module P J := Algebra.toModule
  let : IsFractionRing P J := lpsOriginalReciprocalBaseC_isFractionRing
  let : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
  let : SMul P K := Algebra.toSMul
  let : Module P K := Algebra.toModule
  let : IsScalarTower P J K := .of_algebraMap_eq' rfl
  let : IsScalarTower ℂ P K := .of_algebraMap_eq fun c => by
    change algebraMap J K (algebraMap ℂ J c) =
      algebraMap J K (lpsOriginalComplexJFractionInversion (algebraMap ℂ J c))
    rw [lpsOriginalComplexJFractionInversion_constant]
  let : Module.Finite P R := IsIntegralClosure.finite (A := P) («K» := J) (L := K) R
  let : IsScalarTower ℂ P R := .of_algebraMap_eq fun c => by
    apply IsFractionRing.injective R K
    rw [← IsScalarTower.algebraMap_apply ℂ R K,
      ← IsScalarTower.algebraMap_apply P R K,
      ← IsScalarTower.algebraMap_apply ℂ P K]
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℂ P)
    (inferInstance : Algebra.FiniteType P R)
end QEC.Coding.TannerLiftedProduct
