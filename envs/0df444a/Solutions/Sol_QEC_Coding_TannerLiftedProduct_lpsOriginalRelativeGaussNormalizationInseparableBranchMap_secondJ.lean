-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:49:26.018119+00:00
-- url     : https://prove2.me/submissions/137ae1bf-d20b-4704-84ea-be87688c7998

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationInseparableBranchMap_firstJ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_secondResidueAlternatives
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondJ_not_frobenius

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN))^p =
      AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
        (lpsOriginalGaussMaximalResidueJ N hN p q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let : Algebra (ZMod p) T :=
    ((algebraMap K T).comp (lpsOriginalGaussMaximalResidueConstantMap N hN p q)).toAlgebra
  have h := lpsOriginalRelativeGaussNormalization_secondResidueAlternatives
    N p hNp h4N hN hpN T
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q)
  rw [lpsOriginalRelativeGaussNormalizationInseparableBranchMap_firstJ] at h
  rcases h with h | h
  · exact False.elim ((lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondJ_not_frobenius
      N p hNp h4N hN hpN q) h)
  · exact h
end QEC.Coding.TannerLiftedProduct
