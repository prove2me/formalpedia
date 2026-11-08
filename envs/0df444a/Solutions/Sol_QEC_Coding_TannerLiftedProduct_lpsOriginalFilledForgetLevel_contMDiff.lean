-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_contMDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:06:36.116528+00:00
-- url     : https://prove2.me/submissions/bee32baf-21ad-477b-bdb7-f3b451e03676

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_preferredCuspCoordinates
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspChart_cusp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_target_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_projection_contMDiff
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
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilledChartedSpace M (dvd_trans hN hNM)
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (lpsOriginalFilledForgetLevel N M hNM) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilledChartedSpace M (dvd_trans hN hNM)
  intro x
  cases x with
  | inl y =>
    let eM := lpsOriginalFilledInteriorChart M (dvd_trans hN hNM) y
    let z := eM (Sum.inl y)
    have hz : 0 < z.im := lpsOriginalFilledInteriorChart_target_pos
      M (dvd_trans hN hNM) y z
      (eM.map_source (lpsOriginalFilledInteriorChart_mem M (dvd_trans hN hNM) y))
    have ha : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun z' : ℂ => (Sum.inl ⟦UpperHalfPlane.ofComplex z'⟧ : LPSOriginalFilledCurve N)) z :=
      (lpsOriginalFilled_projection_contMDiff N hN (UpperHalfPlane.ofComplex z)).comp z
        (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) hz)
    apply contMDiffAt_iff_source.mpr
    have he : lpsOriginalFilledForgetLevel N M hNM ∘
        (extChartAt 𝓘(ℂ) (Sum.inl y : LPSOriginalFilledCurve M)).symm =
        (fun z' : ℂ => (Sum.inl ⟦UpperHalfPlane.ofComplex z'⟧ : LPSOriginalFilledCurve N)) := by
      funext z'
      change lpsOriginalFilledForgetLevel N M hNM
        ((lpsOriginalFilledInteriorChart M (dvd_trans hN hNM) y).symm z') = _
      rw [lpsOriginalFilledInteriorChart_symm,lpsOriginalFilledForgetLevel_projection]
    rw [he]
    convert ha.contMDiffWithinAt using 1
    simp only [extChartAt_coe,modelWithCornersSelf_coe]
    rfl
  | inr c =>
    let d := lpsOriginalCuspForgetLevel N M hNM c
    let eM := lpsOriginalFilledCuspChart M c
    let eN := lpsOriginalFilledCuspChart N d
    let e := lpsOriginalCuspLevelDegree N M (lpsOriginalCuspRepresentative M c)
    obtain ⟨α,hα,hαnorm,h⟩ := lpsOriginalFilledForgetLevel_preferredCuspCoordinates N M hNM c
    have he : (fun q : ℂ => eN (lpsOriginalFilledForgetLevel N M hNM (eM.symm q))) =ᶠ[𝓝 0]
        (fun q => α * q ^ e) := by
      have hz : (0 : ℂ) ∈ eM.target :=
        lpsOriginalFilledCuspPartialEquiv_target_zero M (lpsOriginalCuspRepresentative M c)
      filter_upwards [eM.open_target.mem_nhds hz] with q hq
      exact (h q hq).2.2
    have hp : ContDiff ℂ ω (fun q : ℂ => α * q ^ e) :=
      contDiff_const.mul (contDiff_id.pow e)
    have ha := hp.contDiffAt.congr_of_eventuallyEq he
    apply contMDiffAt_iff.mpr
    refine ⟨(lpsOriginalFilledForgetLevel_continuous N M hNM).continuousAt,?_⟩
    convert ha.contDiffWithinAt using 1
    · funext q
      change eN (lpsOriginalFilledForgetLevel N M hNM
        ((extChartAt 𝓘(ℂ) (Sum.inr c : LPSOriginalFilledCurve M)).symm q)) =
          eN (lpsOriginalFilledForgetLevel N M hNM (eM.symm q))
      apply congrArg (fun y => eN (lpsOriginalFilledForgetLevel N M hNM y))
      exact congrFun (extChartAt_coe_symm (I := 𝓘(ℂ))
        (Sum.inr c : LPSOriginalFilledCurve M)) q
    · exact (congrFun (extChartAt_coe (I := 𝓘(ℂ))
        (Sum.inr c : LPSOriginalFilledCurve M)) (Sum.inr c)).trans
          (lpsOriginalFilledCuspChart_cusp M c)
end QEC.Coding.TannerLiftedProduct
