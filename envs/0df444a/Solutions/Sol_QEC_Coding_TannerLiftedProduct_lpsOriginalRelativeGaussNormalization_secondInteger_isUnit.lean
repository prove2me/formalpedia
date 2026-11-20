-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondInteger_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:08:45.216505+00:00
-- url     : https://prove2.me/submissions/b36131ed-833c-4f0c-b60f-32441c8277c3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationLinearBranchMap_secondInteger_isUnit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondInteger_isUnit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationLinearBranchMap_ker
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationInseparableBranchMap_ker
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationCoefficients_isIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationPrimeOver_classification


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    IsUnit (P.eval₂ (Int.castRingHom (LPSOriginalRelativeGaussNormalization N p hNp h4N hN))
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN)) := by
  classical
  let C := LPSOriginalRelativeGaussNormalization N p hNp h4N hN
  let x : C := P.eval₂ (Int.castRingHom C)
    (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN)
  by_contra hx
  have hi : Ideal.span ({x} : Set C) ≠ ⊤ := by
    intro hi
    exact hx (Ideal.span_singleton_eq_top.mp hi)
  obtain ⟨m,hm,hxm⟩ := Ideal.exists_le_maximal (Ideal.span ({x} : Set C)) hi
  let : m.IsMaximal := hm
  let q := m.comap (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
  let : q.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
    (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationCoefficients_isIntegral N p hNp h4N hN hpN) m
  have hmem : x ∈ m := hxm (Ideal.mem_span_singleton_self x)
  rcases lpsOriginalRelativeGaussNormalizationPrimeOver_classification
    N p hNp h4N hN hpN q m rfl with hlin | hins
  · let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    let : Field K := Ideal.Quotient.field q
    have hu := lpsOriginalRelativeGaussNormalizationLinearBranchMap_secondInteger_isUnit
      N p hNp h4N hN hpN q P hP
    rw [hlin,← lpsOriginalRelativeGaussNormalizationLinearBranchMap_ker] at hmem
    exact hu.ne_zero (RingHom.mem_ker.mp hmem)
  · let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
    have hu := lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondInteger_isUnit
      N p hNp h4N hN hpN q P hP
    rw [hins,← lpsOriginalRelativeGaussNormalizationInseparableBranchMap_ker] at hmem
    exact hu.ne_zero (RingHom.mem_ker.mp hmem)
end QEC.Coding.TannerLiftedProduct
