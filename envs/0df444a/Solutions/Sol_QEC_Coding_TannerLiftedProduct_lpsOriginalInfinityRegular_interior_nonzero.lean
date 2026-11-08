-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityRegular_interior_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:02:43.828089+00:00
-- url     : https://prove2.me/submissions/ee3bc0a9-dcc1-476c-8a3b-0d538f543992

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityRegularPoints
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_sub_constant_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_sub_constant_order_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_ne_top
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
theorem _root_.solution
    (x : Q) (hx : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x)
      (algebraMap P K Polynomial.X)⁻¹) : lpsOriginalFilledJ N (Sum.inl x) ≠ 0 := by
  intro hz
  have hp : 0 < lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x)
      (algebraMap P K Polynomial.X) := by
    simpa only [map_zero,sub_zero] using lpsOriginalFieldJ_sub_constant_order_pos N hpos hN 0 x hz
  have hjne : algebraMap P K Polynomial.X ≠ 0 := by
    simpa only [map_zero,sub_zero] using lpsOriginalFieldJ_sub_constant_ne_zero N hpos 0
  have ht := lpsOriginalFieldLocalOrder_ne_top N hN hpos (Sum.inl x) _ hjne
  lift lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X)
    to ℤ using ht with k hk
  have hkpos : 0 < k := by exact_mod_cast hp
  rw [AddValuation.map_inv,←hk,←WithTop.LinearOrderedAddCommGroup.coe_neg] at hx
  have hkneg : 0 ≤ -k := by exact_mod_cast hx
  omega
end QEC.Coding.TannerLiftedProduct
