-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRegularCoefficientSubmodule_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:28:27.24851+00:00
-- url     : https://prove2.me/submissions/4b5d2327-643e-4192-80a3-90ed37e80da4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroDifferentialLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInverseDifferentialLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRegularDifferentialFiniteness
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRegularCoefficientSubmodule_mem_zeroLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_TwoChartFiniteDimensionalBridge_finiteDimensional_of_twoChart_denominator_certificates
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRegularCoefficient_mem_transportedInverseLattice
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTransportedInverseCoefficientRange_finite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroDifferentialCoefficientRange_finite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary001
  LPSOriginalLocalKaehlerFinitenessDictionary002
  LPSOriginalLocalKaehlerFinitenessDictionary003
  LPSOriginalLocalKaehlerFinitenessDictionary004
  LPSOriginalLocalKaehlerFinitenessDictionary005
  LPSOriginalLocalKaehlerFinitenessDictionary006
  LPSOriginalLocalKaehlerFinitenessDictionary007
  LPSOriginalLocalKaehlerFinitenessDictionary008
  LPSOriginalLocalKaehlerFinitenessDictionary009
  LPSOriginalLocalKaehlerFinitenessDictionary010
  LPSOriginalLocalKaehlerFinitenessDictionary011
  LPSOriginalLocalKaehlerFinitenessDictionary012
  LPSOriginalLocalKaehlerFinitenessDictionary013
  LPSOriginalLocalKaehlerFinitenessDictionary014
  LPSOriginalLocalKaehlerFinitenessDictionary015
  LPSOriginalLocalKaehlerFinitenessDictionary016
  LPSOriginalLocalKaehlerFinitenessDictionary017
  LPSOriginalLocalKaehlerFinitenessDictionary018
  LPSOriginalLocalKaehlerFinitenessDictionary031
  LPSOriginalLocalKaehlerFinitenessDictionary032
  LPSOriginalLocalKaehlerFinitenessDictionary033
  LPSOriginalLocalKaehlerFinitenessDictionary034
  LPSOriginalLocalKaehlerFinitenessDictionary035
  LPSOriginalLocalKaehlerFinitenessDictionary036
  LPSOriginalLocalKaehlerFinitenessDictionary037
  LPSOriginalLocalKaehlerFinitenessDictionary038
  LPSOriginalLocalKaehlerFinitenessDictionary039
  LPSOriginalLocalKaehlerFinitenessDictionary040
  LPSOriginalLocalKaehlerFinitenessDictionary041
  LPSOriginalLocalKaehlerFinitenessDictionary042
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_58
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_59
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_60
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_61
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_63
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_65
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_67
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_70
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_71
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_73
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_75
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    FiniteDimensional ℂ (lpsOriginalRegularCoefficientSubmodule N hpos) := by
  classical
  let : Module.Finite P (lpsOriginalZeroDifferentialCoefficientMap N hpos).range :=
    lpsOriginalZeroDifferentialCoefficientRange_finite N hpos
  let b := Module.finBasis (RatFunc ℂ) K
  refine TwoChartFiniteDimensionalBridge.finiteDimensional_of_twoChart_denominator_certificates
    b (lpsOriginalRegularCoefficientSubmodule N hpos)
    (lpsOriginalZeroDifferentialCoefficientMap N hpos).range
    (lpsOriginalRegularCoefficientSubmodule_mem_zeroLattice N hpos) ?_
  dsimp only
  let : Algebra (RatFunc ℂ) K := InverseAffinePlace.transportedRationalAlgebra
    (k := ℂ) (F := K) (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos)
  let : Algebra P K := InverseAffinePlace.transportedPolynomialAlgebra
    (k := ℂ) (F := K) (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos)
  let : SMul P K := Algebra.toSMul
  let : Module P K := Algebra.toModule
  refine ⟨(lpsOriginalTransportedInverseCoefficientMap N hpos).range,
    lpsOriginalTransportedInverseCoefficientRange_finite N hpos, ?_⟩
  intro x
  obtain ⟨omega, homega⟩ := x.property
  rw [← homega]
  exact lpsOriginalRegularCoefficient_mem_transportedInverseLattice N hpos omega
end QEC.Coding.TannerLiftedProduct
