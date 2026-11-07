-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDilatedAtScaledCuspRational
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:21:47.84151+00:00
-- url     : https://prove2.me/submissions/5f130328-7bbb-490c-a832-c76023ff2e80

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_action
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2SLInverse_real_matrix
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) :
    ∃ r : ℚ, ∀ σ : ℍ,
      lpsOriginalJDilated N hN (γ • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant
          (lpsE2AffineMatrix ((Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0))^2)
            (pow_pos (lpsOriginalDilationColumnGcdPos N hN γ) 2) (r:ℝ) • σ) := by
  let g : ℕ := Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)
  have hg : 0<g := lpsOriginalDilationColumnGcdPos N hN γ
  obtain ⟨a,c,hcop,ha,hc⟩ := Int.exists_gcd_one hg
  let δ := lpsE2IntegerPrimitiveColumn a c hcop
  let M : GL (Fin 2) ℝ := lpsE2AffineMatrix N hN 0*Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hdetM : M.det.val=(N:ℝ) := by
    calc M.det.val=(lpsE2AffineMatrix N hN 0).det.val := by simp [M]
         _=(N:ℝ) := lpsE2AffineMatrix_det N hN 0
  have hM00 : M 0 0=((N:ℤ)*γ 0 0:ℤ) := by
    simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
  have hM10 : M 1 0=(γ 1 0:ℝ) := by
    simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
  have hA : (δ 0 0:ℝ)*(g:ℝ)=M 0 0 := by
    rw [hM00]
    change (a:ℝ)*(g:ℝ)=(((N:ℤ)*γ 0 0:ℤ):ℝ)
    exact_mod_cast ha.symm
  have hC : (δ 1 0:ℝ)*(g:ℝ)=M 1 0 := by
    rw [hM10]
    change (c:ℝ)*(g:ℝ)=(γ 1 0:ℝ)
    exact_mod_cast hc.symm
  let h : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹*M
  have hdδ : (δ 0 0:ℝ)*(δ 1 1:ℝ)-(δ 0 1:ℝ)*(δ 1 0:ℝ)=1 := by
    have he : δ 0 0*δ 1 1-δ 0 1*δ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using δ.det_coe
    exact_mod_cast he
  have hh10 : h 1 0=0 := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 1 0=0
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [←hA,←hC]
    ring
  have hh00 : h 0 0=(g:ℝ) := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 0 0=(g:ℝ)
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [←hA,←hC]
    linear_combination (g:ℝ)*hdδ
  have hhdet : h.det.val=(N:ℝ) := by simp [h,hdetM]
  have hgR : (g:ℝ)≠0 := by exact_mod_cast hg.ne'
  have hh11 : h 1 1=(N:ℝ)/(g:ℝ) := by
    apply (eq_div_iff hgR).2
    have he := hhdet
    change Matrix.det (h:Matrix (Fin 2) (Fin 2) ℝ)=(N:ℝ) at he
    simpa only [Matrix.det_fin_two,hh00,hh10,mul_zero,zero_mul,sub_zero,mul_comm] using he
  let b : ℤ := δ 1 1*((N:ℤ)*γ 0 1)-δ 0 1*γ 1 1
  have hh01 : h 0 1=(b:ℝ) := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 0 1=(b:ℝ)
    rw [lpsE2SLInverse_real_matrix]
    simp [M,b,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply,
      Matrix.vecHead,Matrix.vecTail,sub_eq_add_neg]
  let r : ℚ := (b:ℚ)*(g:ℚ)/(N:ℚ)
  have hr : (r:ℝ)=h 0 1*(g:ℝ)/(N:ℝ) := by
    rw [hh01]
    simp only [r,Rat.cast_div,Rat.cast_mul,Rat.cast_intCast,Rat.cast_natCast]
  refine ⟨r,?_⟩
  intro σ
  have hp : 0<h.det.val := by rw [hhdet];exact_mod_cast hN
  have he : h • (lpsE2AffineMatrix N hN 0 • σ)=
      lpsE2AffineMatrix (g^2) (pow_pos hg 2) (r:ℝ) • σ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hp,lpsE2AffineMatrix_action,
      UpperHalfPlane.num,UpperHalfPlane.denom,hh00,hh10,hh11,lpsE2AffineMatrix_action]
    simp only [Complex.ofReal_div,Complex.ofReal_zero,Complex.ofReal_natCast,zero_mul,
      zero_add,add_zero,Nat.cast_pow]
    have hgC : (g:ℂ)≠0 := by exact_mod_cast hg.ne'
    have hNC : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
    rw [hr]
    change ((g:ℂ)*((N:ℂ)*(σ:ℂ))+(h 0 1:ℂ))/((N:ℂ)/(g:ℂ))=
      (g:ℂ)^2*(σ:ℂ)+(h 0 1*(g:ℝ)/(N:ℝ):ℝ)
    push_cast
    field_simp [hgC,hNC]
  have hm : M=Matrix.SpecialLinearGroup.mapGL ℝ δ*h := by simp [h]
  have hγ : ∀ τ : ℍ, γ•τ=Matrix.SpecialLinearGroup.mapGL ℝ γ•τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply,
      UpperHalfPlane.coe_smul_of_det_pos (by simp)]
    simp [UpperHalfPlane.num,UpperHalfPlane.denom,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.map,Matrix.of_apply]
  calc
    lpsOriginalJDilated N hN (γ • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant (M • (lpsE2AffineMatrix N hN 0 • σ)) := by
      simp only [lpsOriginalJDilated,M,mul_smul,hγ]
    _=lpsOriginalJInvariant (Matrix.SpecialLinearGroup.mapGL ℝ δ •
        (h • (lpsE2AffineMatrix N hN 0 • σ))) := by rw [hm,mul_smul]
    _=lpsOriginalJInvariant (h • (lpsE2AffineMatrix N hN 0 • σ)) :=
      lpsOriginalJInvariant_SL_invariant _ ⟨δ,rfl⟩ _
    _=_ := by rw [he]
end QEC.Coding.TannerLiftedProduct
