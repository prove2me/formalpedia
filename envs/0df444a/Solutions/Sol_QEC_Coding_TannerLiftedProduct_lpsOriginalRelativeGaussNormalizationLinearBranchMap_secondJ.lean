-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationLinearBranchMap_secondJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:48:00.998609+00:00
-- url     : https://prove2.me/submissions/b6e3d7ef-2663-4e7b-9f3c-ad42dccdaf4b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationLinearBranchMap_firstJ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_secondResidueAlternatives
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJ_not_prime_power


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) =
      (lpsOriginalGaussMaximalResidueJ N hN p q)^p := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  have h := lpsOriginalRelativeGaussNormalization_secondResidueAlternatives
    N p hNp h4N hN hpN K
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q)
  rw [lpsOriginalRelativeGaussNormalizationLinearBranchMap_firstJ] at h
  rcases h with h | h
  · exact h
  · exact False.elim ((lpsOriginalGaussMaximalResidueJ_not_prime_power N hN p hpN q _) h)
end QEC.Coding.TannerLiftedProduct
