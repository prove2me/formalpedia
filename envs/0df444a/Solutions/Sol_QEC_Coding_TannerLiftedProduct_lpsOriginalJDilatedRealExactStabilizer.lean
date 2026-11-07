-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilatedRealExactStabilizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:30:03.202379+00:00
-- url     : https://prove2.me/submissions/e2cf327f-31ab-4f9f-b7df-b8d3357877b8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilatedExactStabilizer
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N)
    (g : 𝒮ℒ) :
    (∀ τ : ℍ,lpsOriginalJDilated N hN (g.val•τ)=lpsOriginalJDilated N hN τ)↔
      g.val∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
  constructor
  · intro he
    obtain ⟨γ,hγ⟩ := g.property
    have ha : ∀ τ : ℍ,γ•τ=Matrix.SpecialLinearGroup.mapGL ℝ γ•τ := by
      intro τ
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_specialLinearGroup_apply,
        UpperHalfPlane.coe_smul_of_det_pos (by simp)]
      simp [UpperHalfPlane.num,UpperHalfPlane.denom,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
        Matrix.map,Matrix.of_apply]
    have hi : γ∈CongruenceSubgroup.Gamma0 N :=
      (lpsOriginalJDilatedExactStabilizer N hN γ).mp (fun τ=>by rw [ha,hγ];exact he τ)
    exact ⟨γ,hi,hγ⟩
  · intro hg τ
    exact lpsOriginalJDilated_Gamma0_invariant N hN g.val hg τ
end QEC.Coding.TannerLiftedProduct
