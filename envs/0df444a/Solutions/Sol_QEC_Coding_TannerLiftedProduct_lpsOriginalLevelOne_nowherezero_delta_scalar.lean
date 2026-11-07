-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLevelOne_nowherezero_delta_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:29:45.163099+00:00
-- url     : https://prove2.me/submissions/df7c9df4-8af4-4137-815f-e6a0836eaeea

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_surjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelOne_polynomial_j


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ)
    (f : ModularForm 𝒮ℒ (12*(m:ℤ))) (hf : ∀ τ : ℍ, f τ≠0) :
    ∃ c : ℂ, c≠0 ∧ ∀ τ : ℍ, f τ=c*ModularForm.discriminant τ^m := by
  obtain ⟨P,_,hp⟩ := lpsOriginalLevelOne_polynomial_j m f
  have hr : ∀ z : ℂ, P.eval z≠0 := by
    intro z hz
    obtain ⟨τ,hτ⟩ := lpsOriginalJInvariant_surjective z
    apply hf τ
    rw [hp τ,hτ,hz,mul_zero]
  have hd : P.degree=0 := by
    by_contra h
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_root P h
    exact hr z hz
  have hc : P=Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_degree_le_zero hd.le
  refine ⟨P.coeff 0,?_,?_⟩
  · intro h
    apply hf UpperHalfPlane.I
    rw [hp UpperHalfPlane.I,hc,Polynomial.eval_C,h,mul_zero]
  · intro τ
    rw [hp τ,hc,Polynomial.eval_C,Polynomial.coeff_C_zero,mul_comm]
end QEC.Coding.TannerLiftedProduct
