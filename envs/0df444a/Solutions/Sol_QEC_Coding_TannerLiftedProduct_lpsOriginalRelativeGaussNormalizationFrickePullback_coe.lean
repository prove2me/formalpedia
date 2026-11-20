-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFrickePullback_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:40:22.447093+00:00
-- url     : https://prove2.me/submissions/0f338350-7106-48eb-84b8-12b7e7e36309

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondResidueDegrees
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (x : LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN x).val =
      lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos) x.val := by
  rfl
end QEC.Coding.TannerLiftedProduct
