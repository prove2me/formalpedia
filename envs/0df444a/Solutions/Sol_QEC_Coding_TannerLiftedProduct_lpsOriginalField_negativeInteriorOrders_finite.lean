-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalField_negativeInteriorOrders_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:07:50.482294+00:00
-- url     : https://prove2.me/submissions/6adb1080-3a36-4508-94b3-aed732e092c5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_representative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_finite_nonanalytic
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteNegativeDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f : K) :
    {x : Q | lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f < 0}.Finite := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  obtain ⟨F,hF⟩ := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict_surjective
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f)
  have hbad := lpsOriginalFilledChartMeromorphic_finite_nonanalytic N hN F.val F.property
  apply (Set.Finite.preimage Sum.inl_injective.injOn hbad).subset
  intro x hx
  change ¬ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F.val (Sum.inl x)
  intro ha
  have hd := contMDiffAt_iff_source.mp ha
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hd
  have hc : ContDiffAt ℂ ω (F.val ∘ (lpsOriginalLocalChart N hN (Sum.inl x)).symm)
      (lpsOriginalLocalChartCenter N hN (Sum.inl x)) := by
    simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm,Set.range_id,Function.comp_def,id_eq,
      contDiffWithinAt_univ,lpsOriginalLocalChart,lpsOriginalLocalChartCenter] using hd
  have hn : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f := by
    rw [lpsOriginalFieldLocalOrder_value,
      lpsOriginalFieldToLocal_representative N hN hpos (Sum.inl x) f F hF]
    exact hc.analyticAt.meromorphicAt.meromorphicOrderAt_nonneg_iff.mpr
      ⟨_,hc.analyticAt,Filter.EventuallyEq.rfl⟩
  exact (not_le_of_gt hx) hn
end QEC.Coding.TannerLiftedProduct
