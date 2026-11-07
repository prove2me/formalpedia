-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspChange_translation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:05.303025+00:00
-- url     : https://prove2.me/submissions/b3b34c55-3546-42c9-be7d-a9ac3fe87a88

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspOrbit_eq_iff_original_action
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralFixInfinity_translation
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
theorem _root_.solution (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ') :
    ∃ g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      ∃ x : ℝ,
        (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹*g*Matrix.SpecialLinearGroup.mapGL ℝ ρ'=
          Matrix.GeneralLinearGroup.upperRightHom x ∨
        (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹*g*Matrix.SpecialLinearGroup.mapGL ℝ ρ'=
          -Matrix.GeneralLinearGroup.upperRightHom x := by
  obtain ⟨g,hg,he⟩ := (lpsOriginalCuspOrbit_eq_iff_original_action N ρ ρ').mp h
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let e := Matrix.SpecialLinearGroup.mapGL ℝ ρ'
  let d := r⁻¹*g*e
  have hd : d∈(Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range := by
    obtain ⟨γ,hγ,hγg⟩ := hg
    refine ⟨ρ⁻¹*γ*ρ',?_⟩
    simp only [map_mul,map_inv]
    rw [hγg]
  have hf : d • (OnePoint.infty : OnePoint ℝ)=OnePoint.infty := by
    simp only [d,mul_smul]
    rw [he]
    exact inv_smul_smul r OnePoint.infty
  obtain ⟨x,hx⟩ := lpsIntegralFixInfinity_translation d hd
    (OnePoint.smul_infty_eq_self_iff.mp hf)
  exact ⟨g,hg,x,hx⟩
end QEC.Coding.TannerLiftedProduct
