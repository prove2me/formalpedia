-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_interior_cusp_differential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:55:32.805567+00:00
-- url     : https://prove2.me/submissions/19d8617f-3668-4774-94b8-c5bb3a7c5d9b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoordinate_differential_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspChart_source
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_target_pos
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
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledInteriorChart N hN x).symm.trans
        (lpsOriginalFilledCuspChart N c)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledCuspChart N c)
    lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) (e z) *
      deriv e z = f (UpperHalfPlane.ofComplex z) := by
  let := lpsOriginalFilledTopology N
  change z∈(lpsOriginalFilledInteriorChart N hN x).target ∧
    (lpsOriginalFilledInteriorChart N hN x).symm z∈
      (lpsOriginalFilledCuspChart N c).source at hz
  have hp := lpsOriginalFilledInteriorChart_target_pos N hN x z hz.1
  let τ : ℍ := ⟨z,hp⟩
  have hx := hz.2
  rw [lpsOriginalFilledInteriorChart_symm] at hx
  rw [lpsOriginalFilledCuspChart_source,UpperHalfPlane.ofComplex_apply_of_im_pos hp] at hx
  have hd := lpsOriginalCuspCoordinate_differential_pullback N f
    (lpsOriginalCuspRepresentative N c) τ hx
  have he : (((lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledCuspChart N c)) : ℂ→ℂ)=
      (fun w : ℂ => lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)
        (Sum.inl (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex w)))) := by
    funext w
    rw [OpenPartialHomeomorph.trans_apply,lpsOriginalFilledInteriorChart_symm]
    rfl
  dsimp only
  rw [he]
  simpa only [τ,UpperHalfPlane.ofComplex_apply_of_im_pos hp] using hd
end QEC.Coding.TannerLiftedProduct
