-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJFibre_inverse_not_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:29:08.704522+00:00
-- url     : https://prove2.me/submissions/3c763aa4-3b28-4482-bf04-03c26df7c433

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_sub_constant_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_ne_top
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_j
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_interior_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
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
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
include hpos
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℂ) (y : Q)
    (hy : lpsOriginalFilledJ N (Sum.inl y) = a) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ¬ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ((lpsOriginalFilledJ N - fun _ => a)⁻¹) (Sum.inl y) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := lpsOriginalFilledInteriorChart N hN y
  let z := e (Sum.inl y)
  let f : ℂ → ℂ := fun w => lpsOriginalFilledJ N (e.symm w) - a
  have hs := lpsOriginalFilledInteriorChart_mem N hN y
  have ha : AnalyticAt ℂ f z :=
    (lpsOriginalFilledJ_interior_analytic N hN y z (e.map_source hs)).sub analyticAt_const
  have hv : f z = 0 := by dsimp only [f,z];rw [e.left_inv hs,hy,sub_self]
  have hp : 0 < meromorphicOrderAt f z :=
    (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp
      (by simpa only [hv] using ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hn := lpsOriginalFieldLocalOrder_ne_top N hN hpos (Sum.inl y)
    (algebraMap P K Polynomial.X - algebraMap ℂ K a) (lpsOriginalFieldJ_sub_constant_ne_zero N hpos a)
  rw [lpsOriginalFieldLocalOrder_value,map_sub,lpsOriginalFieldToLocal_j,
    lpsOriginalFieldToLocal_constant] at hn
  change meromorphicOrderAt f z ≠ ⊤ at hn
  lift meromorphicOrderAt f z to ℤ using hn with k hk
  have hkpos : 0 < k := by exact_mod_cast hp
  intro hbad
  have hchart : chartAt ℂ (Sum.inl y : LPSOriginalFilledCurve N) = e := rfl
  have hd := contMDiffAt_iff_source.mp hbad
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hd
  have hi : AnalyticAt ℂ f⁻¹ z := by
    have hc : ContDiffAt ℂ ω f⁻¹ z := by
      simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm,Set.range_id,Function.comp_def,id_eq,
        contDiffWithinAt_univ,hchart,Pi.inv_def,Pi.inv_apply,Pi.sub_apply,f,z,e] using hd
    exact hc.analyticAt
  have hnon : 0 ≤ meromorphicOrderAt f⁻¹ z :=
    hi.meromorphicAt.meromorphicOrderAt_nonneg_iff.mpr ⟨f⁻¹,hi,Filter.EventuallyEq.rfl⟩
  rw [meromorphicOrderAt_inv,←hk,←WithTop.LinearOrderedAddCommGroup.coe_neg] at hnon
  have : 0 ≤ -k := by exact_mod_cast hnon
  exact (not_le_of_gt (neg_neg_of_pos hkpos)) this
end QEC.Coding.TannerLiftedProduct
