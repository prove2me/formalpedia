-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:25:35.503646+00:00
-- url     : https://prove2.me/submissions/b15f4472-76f6-4e47-b0d2-966053c1052f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_holomorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_holomorphic_eq_const
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_nonconstant


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : Function.Surjective lpsOriginalJInvariant := by
  intro a
  by_contra h
  have ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a := by
    intro τ ht
    exact h ⟨τ,ht⟩
  obtain ⟨c,hc⟩ := lpsOriginalFilled_holomorphic_eq_const 4 (by decide)
    (lpsOriginalFilledJReciprocal 4 a)
    (lpsOriginalFilledJReciprocal_holomorphic 4 (by decide) a ho)
  apply lpsOriginalJInvariant_nonconstant
  refine ⟨lpsOriginalJInvariant UpperHalfPlane.I,fun τ => ?_⟩
  have ht := congr_fun hc (Sum.inl ⟦τ⟧)
  have hi := congr_fun hc (Sum.inl ⟦UpperHalfPlane.I⟧)
  have he : (lpsOriginalJInvariant τ-a)⁻¹=(lpsOriginalJInvariant UpperHalfPlane.I-a)⁻¹ :=
    ht.trans hi.symm
  exact sub_left_inj.mp (inv_injective he)
end QEC.Coding.TannerLiftedProduct
