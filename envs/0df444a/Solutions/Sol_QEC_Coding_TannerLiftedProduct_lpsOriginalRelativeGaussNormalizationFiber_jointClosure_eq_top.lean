-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiber_jointClosure_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:56:22.398788+00:00
-- url     : https://prove2.me/submissions/29900fac-e0c6-4b80-a64f-fe002cabfee7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFrobeniusPair_subring_eq_top
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJN_not_prime_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second
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
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Subring.closure
      (Set.range (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q) ∪
        Set.range (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q)) = ⊤ := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
  let S := Subring.closure
    (Set.range (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q) ∪
      Set.range (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q))
  have hT : S.comap e.symm.toRingHom = ⊤ := by
    refine lpsOriginalFrobeniusPair_subring_eq_top p _ ?_ ?_
      (lpsOriginalGaussMaximalResidueJN N hN p q) ?_
    · intro a
      change e.symm (a, a^p) ∈ S
      have h := RingHom.congr_fun
        (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first
          N p hNp h4N hN hpN q) a
      change e (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q a) =
        (a, a^p) at h
      rw [← h, e.symm_apply_apply]
      exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    · intro a
      change e.symm (a^p, a) ∈ S
      have h := RingHom.congr_fun
        (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second
          N p hNp h4N hN hpN q) a
      change e (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q a) =
        (a^p, a) at h
      rw [← h, e.symm_apply_apply]
      exact Subring.subset_closure (Or.inr ⟨a, rfl⟩)
    · exact lpsOriginalGaussMaximalResidueJN_not_prime_power N hN p hpN q
        ((lpsOriginalGaussMaximalResidueJN N hN p q)^p)
  apply top_unique
  intro x _hx
  have h : e x ∈ S.comap e.symm.toRingHom := by rw [hT]; trivial
  change e.symm (e x) ∈ S at h
  simpa using h
end QEC.Coding.TannerLiftedProduct
