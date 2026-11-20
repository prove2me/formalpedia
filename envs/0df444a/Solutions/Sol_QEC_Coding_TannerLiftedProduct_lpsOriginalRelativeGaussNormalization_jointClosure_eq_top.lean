-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_jointClosure_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:59:26.701964+00:00
-- url     : https://prove2.me/submissions/fb90a9f6-be23-420c-a0ba-72129bc8c28a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAdjoinRoot_subring_eq_top
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_root
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
open scoped TensorProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    Subring.closure (Set.range (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) ∪
      Set.range (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN)) = ⊤ := by
  let e := lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
  let S := Subring.closure
    (Set.range (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) ∪
      Set.range (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN))
  have hT : S.comap e.toRingHom = ⊤ := by
    apply lpsOriginalAdjoinRoot_subring_eq_top (lpsOriginalRelativeGaussHeckePolynomial N hN p)
    · intro r
      exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
    · change lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN ∈ S
      rw [← lpsOriginalRelativeGaussNormalizationSecondOrderMap_root]
      exact Subring.subset_closure (Or.inr ⟨_, rfl⟩)
  apply top_unique
  intro x _hx
  have h : e.symm x ∈ S.comap e.toRingHom := by rw [hT]; trivial
  change e (e.symm x) ∈ S at h
  simpa using h
end QEC.Coding.TannerLiftedProduct
