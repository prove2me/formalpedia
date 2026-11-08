-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityEvaluation_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:05:09.063393+00:00
-- url     : https://prove2.me/submissions/6f6d2a76-e8b2-422e-a0a8-a481daf66c96

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityRegularPoints
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityPolynomialChartMap_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityConstantChart_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalChartEvaluation_constant
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
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityRegularPointsDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityRegularPointsDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityRegularPointsDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityRegularPointsDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (x : S) (p : P) :
    lpsOriginalInfinityNormalChartEvaluation N hpos hN x.val x.property
      (lpsOriginalInfinityPolynomialChartMap N hpos p) =
        p.eval (lpsOriginalInfinityCoordinate N hpos hN x) := by
  let E := lpsOriginalInfinityNormalChartEvaluation N hpos hN x.val x.property
  have hh : E.comp (lpsOriginalInfinityPolynomialChartMap N hpos) =
      Polynomial.evalRingHom (lpsOriginalInfinityCoordinate N hpos hN x) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,Polynomial.coe_evalRingHom,Polynomial.eval_C]
      have hc : lpsOriginalInfinityPolynomialChartMap N hpos (Polynomial.C c) =
          lpsOriginalComplexInfinityConstantRingHom N hpos c := by
        apply Subtype.ext
        rw [lpsOriginalInfinityPolynomialChartMap_value,
          lpsOriginalInfinityConstantChart_value,lpsOriginalReciprocalFieldPolynomialMap_eval]
        simp
      rw [hc]
      exact lpsOriginalInfinityNormalChartEvaluation_constant N hpos hN x.val x.property c
    · simp only [RingHom.comp_apply,Polynomial.coe_evalRingHom,Polynomial.eval_X]
      rfl
  exact RingHom.congr_fun hh p
end QEC.Coding.TannerLiftedProduct
