-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityCoordinate_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:07:18.77627+00:00
-- url     : https://prove2.me/submissions/f932f1cb-efbc-484c-95cd-064d8df61256

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityRegularPoints
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityPolynomialChartMap_value
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_meromorphicNoPoleEvaluation_rep
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_interior_order_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_inverse_interior_order_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_sub_constant_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_j
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_interior_analytic
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
theorem _root_.solution (x : Q)
    (hx : lpsOriginalFilledJ N (Sum.inl x) ≠ 0) :
    lpsOriginalInfinityCoordinate N hpos hN
      ⟨Sum.inl x,lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx⟩ =
        (lpsOriginalFilledJ N (Sum.inl x))⁻¹ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let e := lpsOriginalFilledInteriorChart N hN x
  let z := e (Sum.inl x)
  have hcenter : lpsOriginalLocalChartCenter N hN (Sum.inl x) = z := rfl
  have hs := lpsOriginalFilledInteriorChart_mem N hN x
  have ha := lpsOriginalFilledJ_interior_analytic N hN x z (e.map_source hs)
  let A : (AddValuation.toValuation (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN (Sum.inl x)))).integer :=
    ⟨lpsOriginalFieldToLocal N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X),by
      change 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X)
      exact lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x⟩
  let B : (AddValuation.toValuation (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN (Sum.inl x)))).integer :=
    lpsOriginalInfinityNormalChartToMeromorphicInteger N hpos hN (Sum.inl x)
    (lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx)
    (lpsOriginalInfinityPolynomialChartMap N hpos Polynomial.X)
  have hB : B.val = lpsOriginalFieldToLocal N hN hpos (Sum.inl x)
      (algebraMap P K Polynomial.X)⁻¹ := by
    change lpsOriginalFieldToLocal N hN hpos (Sum.inl x)
      (lpsOriginalInfinityPolynomialChartMap N hpos Polynomial.X).val = _
    rw [lpsOriginalInfinityPolynomialChartMap_value,
      lpsOriginalReciprocalFieldPolynomialMap_eval,Polynomial.eval₂_X]
  have hjne : algebraMap P K Polynomial.X ≠ 0 := by
    simpa only [map_zero,sub_zero] using lpsOriginalFieldJ_sub_constant_ne_zero N hpos 0
  have hm : A*B = 1 := by
    apply Subtype.ext
    change lpsOriginalFieldToLocal N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X) * B.val = 1
    rw [hB,←map_mul,mul_inv_cancel₀ hjne,map_one]
  have hAval : meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN (Sum.inl x)) A = lpsOriginalFilledJ N (Sum.inl x) := by
    have he : meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN (Sum.inl x)) A =
        lpsOriginalFilledJ N (e.symm (lpsOriginalLocalChartCenter N hN (Sum.inl x))) := by
      apply meromorphicNoPoleEvaluation_rep _ _ (fun w => lpsOriginalFilledJ N (e.symm w))
        (by simpa only [hcenter] using ha)
      change (lpsOriginalFieldToLocal N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X)).val = _
      rw [lpsOriginalFieldToLocal_j]
      rfl
    have hpoint : e.symm (lpsOriginalLocalChartCenter N hN (Sum.inl x)) = Sum.inl x := by
      rw [hcenter]
      exact e.left_inv hs
    rwa [hpoint] at he
  have hmul : lpsOriginalFilledJ N (Sum.inl x) *
      lpsOriginalInfinityCoordinate N hpos hN
        ⟨Sum.inl x,lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx⟩ = 1 := by
    have h := congrArg (meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN (Sum.inl x))) hm
    rw [map_mul,map_one,hAval] at h
    exact h
  calc
    _ = lpsOriginalInfinityCoordinate N hpos hN
      ⟨Sum.inl x,lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx⟩ *
        (lpsOriginalFilledJ N (Sum.inl x) * (lpsOriginalFilledJ N (Sum.inl x))⁻¹) := by
          rw [mul_inv_cancel₀ hx,mul_one]
    _ = (lpsOriginalFilledJ N (Sum.inl x) *
      lpsOriginalInfinityCoordinate N hpos hN
        ⟨Sum.inl x,lpsOriginalFieldJ_inverse_interior_order_nonnegative N hpos hN x hx⟩) *
        (lpsOriginalFilledJ N (Sum.inl x))⁻¹ := by ring
    _ = _ := by rw [hmul,one_mul]
end QEC.Coding.TannerLiftedProduct
