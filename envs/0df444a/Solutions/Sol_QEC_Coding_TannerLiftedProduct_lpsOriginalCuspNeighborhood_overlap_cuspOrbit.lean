-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspNeighborhood_overlap_cuspOrbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:15.641796+00:00
-- url     : https://prove2.me/submissions/2be328d3-5799-4617-8005-2be123b7807f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspOrbit_eq_of_original_cusp_action
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2,ℤ)) (τ σ : {τ : ℍ // 1<τ.im})
    (he : lpsOriginalCuspProjection N ρ τ=lpsOriginalCuspProjection N ρ' σ) :
    lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ' := by
  have ho := Quotient.eq.mp he
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at ho
  obtain ⟨g,hg⟩ := ho
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let e := Matrix.SpecialLinearGroup.mapGL ℝ ρ'
  let d := r⁻¹*g.val*e
  have hd : d∈(Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range := by
    obtain ⟨γ,hγ,hγg⟩ := g.property
    refine ⟨ρ⁻¹*γ*ρ',?_⟩
    simp only [map_mul,map_inv]
    rw [hγg]
  have hs : d • σ.val=τ.val := by
    change (r⁻¹*g.val*e) • σ.val=τ.val
    simp only [mul_smul]
    change r⁻¹ • (g • (e • σ.val))=τ.val
    rw [hg]
    exact inv_smul_smul r τ.val
  have hz := lpsIntegralHoroball_lowerLeft_zero d hd σ.val σ.property (hs ▸ τ.property)
  have hf : d • (OnePoint.infty : OnePoint ℝ)=OnePoint.infty := OnePoint.smul_infty_eq_self_iff.mpr hz
  apply lpsOriginalCuspOrbit_eq_of_original_cusp_action N ρ ρ' g.val g.property
  have ht := congrArg (fun c : OnePoint ℝ => r • c) hf
  simpa only [d,mul_smul,smul_inv_smul] using ht
end QEC.Coding.TannerLiftedProduct
