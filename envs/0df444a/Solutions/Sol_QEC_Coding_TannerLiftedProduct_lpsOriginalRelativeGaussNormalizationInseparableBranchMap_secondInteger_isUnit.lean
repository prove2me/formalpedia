-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondInteger_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:02:21.986379+00:00
-- url     : https://prove2.me/submissions/cb179f2f-a554-4bd0-ae07-ee71db9ebc77

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__hom_5c9005d9bf86
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_integerPolynomial_isUnit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_j


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    IsUnit (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (P.eval₂ (Int.castRingHom (LPSOriginalRelativeGaussNormalization N p hNp h4N hN))
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN))) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q
  have h := (lpsOriginalGaussMaximalResidue_integerPolynomial_isUnit N hN p q P hP).map
    e.symm.toRingHom
  rw [lpsOriginalIntegerPolynomial_eval₂_hom] at h
  have he : e.symm.toRingHom (lpsOriginalGaussMaximalResidueJ N hN p q) =
      lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) :=
    lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_j N p hNp h4N hN hpN q
  rw [he] at h
  rw [lpsOriginalIntegerPolynomial_eval₂_hom]
  exact h
end QEC.Coding.TannerLiftedProduct
