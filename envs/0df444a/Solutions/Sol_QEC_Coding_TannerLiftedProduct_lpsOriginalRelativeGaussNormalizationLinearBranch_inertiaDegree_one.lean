-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationLinearBranch_inertiaDegree_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:37:26.469975+00:00
-- url     : https://prove2.me/submissions/381c1280-390e-4aa5-8a98-92457eceb829

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_maximal

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q).inertiaDeg (LPSOriginalGaussAffineOrder N hN p) = 1 := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_liesOver N p hNp h4N hN hpN q
  let : Algebra (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (le_of_eq (lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_liesOver N p hNp h4N hN hpN q).over)
  let : Module (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) := Algebra.toModule
  rw [Ideal.inertiaDeg_eq_of_isMaximal q]
  exact (lpsOriginalRelativeGaussNormalizationLinearBranchResidueEquiv N p hNp h4N hN hpN q).toLinearEquiv.finrank_eq.trans
    (Module.finrank_self _)
end QEC.Coding.TannerLiftedProduct
