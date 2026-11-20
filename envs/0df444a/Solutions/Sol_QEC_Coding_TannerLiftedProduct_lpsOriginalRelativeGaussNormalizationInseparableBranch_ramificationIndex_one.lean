-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranch_ramificationIndex_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:49:56.601284+00:00
-- url     : https://prove2.me/submissions/be5d873e-c99f-4d7e-a42f-a3c420cd41ed

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_dedekind
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_maximal
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationBranchIdeals_coprime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationBranchIdeals_product
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCoprimeMaximalIdeal_factorCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCoprimeMaximalIdeal_ne_bot


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).ramificationIdx (LPSOriginalGaussAffineOrder N hN p) = 1 := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalization_dedekind N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q
  have hc := lpsOriginalRelativeGaussNormalizationBranchIdeals_coprime N p hNp h4N hN hpN q
  have hi := lpsOriginalCoprimeMaximalIdeal_ne_bot _ _ hc
  have hj := lpsOriginalCoprimeMaximalIdeal_ne_bot _ _ hc.symm
  have hm : q.map (algebraMap (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN)) ≠ ⊥ := by
    change q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) ≠ ⊥
    rw [← lpsOriginalRelativeGaussNormalizationBranchIdeals_product N p hNp h4N hN hpN q]
    exact mul_ne_zero hi hj
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count q _ hm]
  change (UniqueFactorizationMonoid.normalizedFactors (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))).count (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) = 1
  rw [← lpsOriginalRelativeGaussNormalizationBranchIdeals_product N p hNp h4N hN hpN q,
    mul_comm (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q)
      (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q)]
  exact lpsOriginalCoprimeMaximalIdeal_factorCount _ _ hc.symm
end QEC.Coding.TannerLiftedProduct
