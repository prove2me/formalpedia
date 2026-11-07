-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGamma0_projected_im_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:22.123823+00:00
-- url     : https://prove2.me/submissions/2cd6a825-098a-40e2-b892-3779c03ab8b8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegral_im_bound
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
theorem _root_.solution (N : ℕ) (ρ : SL(2,ℤ)) (τ σ : ℍ)
    (h : lpsOriginalGamma0Projected N ρ τ=
      (⟦σ⟧ : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)) :
    τ.im≤ max σ.im (1/σ.im) := by
  have ho := Quotient.eq.mp h
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at ho
  obtain ⟨g,hg⟩ := ho
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let d := r⁻¹*g.val
  have hd : d∈(Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range := by
    obtain ⟨γ,hγ,hγg⟩ := g.property
    refine ⟨ρ⁻¹*γ,?_⟩
    simp only [map_mul,map_inv]
    rw [hγg]
  have hs : d • σ=τ := by
    simp only [d,mul_smul]
    change r⁻¹ • (g • σ)=τ
    rw [hg]
    exact inv_smul_smul r τ
  simpa only [hs] using lpsIntegral_im_bound d hd σ
end QEC.Coding.TannerLiftedProduct
