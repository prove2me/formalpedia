-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_cusp_interior_differential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:58:29.043095+00:00
-- url     : https://prove2.me/submissions/eac430a8-4c74-4926-b87f-f65388a5144a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_interior_cusp_differential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOpenPartialHomeomorph_inverse_deriv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_interior_cusp_analytic
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
      z∈((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledInteriorChart N hN x)).source) :
    letI := lpsOriginalFilledTopology N
    let e := (lpsOriginalFilledCuspChart N c).symm.trans
      (lpsOriginalFilledInteriorChart N hN x)
    f (UpperHalfPlane.ofComplex (e z)) * deriv e z =
      lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) z := by
  let := lpsOriginalFilledTopology N
  let e := (lpsOriginalFilledCuspChart N c).symm.trans
    (lpsOriginalFilledInteriorChart N hN x)
  have hf := lpsOriginalFilled_interior_cusp_differential N hN f x c (e z)
    (e.map_source hz)
  have ha := lpsOriginalFilled_interior_cusp_analytic N hN x c (e z) (e.map_source hz)
  have hi := lpsOpenPartialHomeomorph_inverse_deriv e.symm (e z)
    (e.map_source hz) ha.1 ha.2
  have hsym : e.symm=(lpsOriginalFilledInteriorChart N hN x).symm.trans
      (lpsOriginalFilledCuspChart N c) := by
    simp only [e,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  rw [←hsym] at hf
  have hf' : lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) z *
      deriv e.symm (e z) = f (UpperHalfPlane.ofComplex (e z)) := by
    simpa only [e.left_inv hz] using hf
  have hi' : deriv e z * deriv e.symm (e z) = 1 := by
    simpa only [OpenPartialHomeomorph.symm_symm,e.left_inv hz] using hi
  dsimp only
  rw [←hf',mul_assoc,mul_comm (deriv e.symm (e z)) (deriv e z),hi',mul_one]
end QEC.Coding.TannerLiftedProduct
