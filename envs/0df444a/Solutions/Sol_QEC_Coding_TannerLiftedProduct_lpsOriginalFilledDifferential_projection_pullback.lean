-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferential_projection_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:15:48.171433+00:00
-- url     : https://prove2.me/submissions/a7d69322-f34c-4ef2-aa3c-c3930ea88fc7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_projection_differential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    let proj : ℍ→LPSOriginalFilledCurve N := fun σ => Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ)
    lpsOriginalFilledDifferential N hN f (proj τ)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) proj τ v) = lpsCuspDifferential N f τ v := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let proj : ℍ→LPSOriginalFilledCurve N := fun σ => Sum.inl (Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) σ)
  have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) proj τ :=
    (lpsOriginalFilled_projection_contMDiff N hN τ).mdifferentiableAt (by decide)
  have hd := lpsOriginalFilledInteriorChart_projection_differential N hN f
    (Quotient.mk _ τ) τ (lpsOriginalFilledInteriorChart_mem N hN (Quotient.mk _ τ))
  let D : ℂ→L[ℂ]ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) proj τ
  dsimp only
  change f (UpperHalfPlane.ofComplex (lpsOriginalFilledInteriorChart N hN (Quotient.mk _ τ) (proj τ))) *
    D v = f τ*v
  have hder : D=
      fderivWithin ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) τ proj)
        (Set.range 𝓘(ℂ)) (extChartAt 𝓘(ℂ) τ τ) := by
    exact if_pos hm
  rw [hder]
  simp only [modelWithCornersSelf_coe,Set.range_id,fderivWithin_univ]
  change f (UpperHalfPlane.ofComplex (lpsOriginalFilledInteriorChart N hN (Quotient.mk _ τ) (proj τ))) *
    (fderiv ℂ (fun z : ℂ => lpsOriginalFilledInteriorChart N hN (Quotient.mk _ τ)
      (proj (UpperHalfPlane.ofComplex z))) (τ:ℂ)) v = f τ*v
  rw [fderiv_eq_deriv_mul,←mul_assoc]
  simpa only [proj,UpperHalfPlane.ofComplex_apply] using congrArg (fun z : ℂ => z*v) hd
end QEC.Coding.TannerLiftedProduct
