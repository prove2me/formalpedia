-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranchResidue_purelyInseparable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:39:25.215441+00:00
-- url     : https://prove2.me/submissions/473925a0-ef2b-40f3-9a7f-1010dbc7df00

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussInseparableBranch_purelyInseparable


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    letI := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal N p hNp h4N hN hpN q
    letI := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q
    letI : Field (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) :=
      Ideal.Quotient.field _
    IsPurelyInseparable (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q
  let : Field (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) := Ideal.Quotient.field _
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let := lpsOriginalRelativeGaussInseparableBranch_purelyInseparable N hN p hpN q
  exact (lpsOriginalRelativeGaussNormalizationInseparableBranchResidueEquiv N p hNp h4N hN hpN q).symm.isPurelyInseparable
end QEC.Coding.TannerLiftedProduct
