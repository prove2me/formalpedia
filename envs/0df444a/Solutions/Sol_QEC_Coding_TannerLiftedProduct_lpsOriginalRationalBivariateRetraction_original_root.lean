-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalBivariateRetraction_original_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:39:04.441111+00:00
-- url     : https://prove2.me/submissions/19d75628-2278-4f0c-9f65-8671516dc6de

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedRationalCusp_zero_germ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalBivariateRetraction_eval
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedRationalCusp_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_holomorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_holomorphic
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
theorem _root_.solution
    (N : ℕ) (hN : 0<N) (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) : ∀ τ : ℍ,
      (lpsOriginalRationalBivariateRetraction P).eval₂
        ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
          (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0 := by
  classical
  let F : ℍ→ℂ := ∑ k∈P.support,∑ i∈(P.coeff k).support,
    fun τ=> (lpsOriginalRationalRetraction ((P.coeff k).coeff i):ℂ)*
      lpsOriginalJInvariant τ^i*lpsOriginalJDilated N hN τ^k
  have hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
    exact MDifferentiable.sum fun k _=>MDifferentiable.sum fun i _=>
      (mdifferentiable_const.mul (lpsOriginalJInvariant_holomorphic.pow i)).mul
        ((lpsOriginalJDilated_holomorphic N hN).pow k)
  have heval (τ : ℍ) :
      (lpsOriginalRationalBivariateRetraction P).eval₂
        ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
          (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=F τ := by
    rw [lpsOriginalRationalBivariateRetraction_eval]
    simp only [F,Finset.sum_apply]
  let G := lpsOriginalClearedRationalCusp N (lpsOriginalClearingBound N P) P
  have hg : G=ᶠ[𝓝 (0:ℂ)]0 := lpsOriginalClearedRationalCusp_zero_germ N hN P hroot
  obtain ⟨s,hs,hopen,h0⟩ := eventually_nhds_iff.mp hg
  obtain ⟨τ,hτ⟩ : ∃ τ : ℍ,Function.Periodic.qParam 1 (τ:ℂ)∈s :=
    ((UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1)).eventually
      (hopen.mem_nhds h0)).exists
  have hnear : ∀ᶠ z : ℍ in 𝓝 τ,Function.Periodic.qParam 1 (z:ℂ)∈s :=
    ((Function.Periodic.continuous_qParam.comp UpperHalfPlane.continuous_coe).continuousAt.tendsto).eventually
      (hopen.mem_nhds hτ)
  have hzero : ∀ᶠ z : ℍ in 𝓝 τ,F z=0 := by
    filter_upwards [hnear] with z hz
    have h := hs _ hz
    change lpsOriginalClearedRationalCusp N (lpsOriginalClearingBound N P) P (Function.Periodic.qParam 1 (z:ℂ))=0 at h
    rw [lpsOriginalClearedRationalCusp_pullback N hN P z,heval] at h
    exact (mul_eq_zero.mp h).resolve_left
      (pow_ne_zero _ (Function.Periodic.qParam_ne_zero _))
  have hfzero : F=0 := UpperHalfPlane.eq_zero_of_frequently hF
    ((hzero.filter_mono nhdsWithin_le_nhds).frequently)
  intro z
  rw [heval,hfzero]
  rfl
end QEC.Coding.TannerLiftedProduct
