-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranch_secondInertiaDegree_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:38:30.483182+00:00
-- url     : https://prove2.me/submissions/cb749e45-213e-4ae0-87e1-b42b5e8b6f0a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondResidueDegrees

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).inertiaDeg
      (LPSOriginalGaussAffineOrder N hN p) = 1 := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_secondLiesOver N p hNp h4N hN hpN q
  let : Algebra K (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (le_of_eq (lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_secondLiesOver
        N p hNp h4N hN hpN q).over)
  let : Module K (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) := Algebra.toModule
  rw [Ideal.inertiaDeg_eq_of_isMaximal q]
  exact (lpsOriginalRelativeGaussNormalizationInseparableBranchSecondResidueAlgEquiv
    N p hNp h4N hN hpN q).toLinearEquiv.finrank_eq.trans (Module.finrank_self K)
end QEC.Coding.TannerLiftedProduct
