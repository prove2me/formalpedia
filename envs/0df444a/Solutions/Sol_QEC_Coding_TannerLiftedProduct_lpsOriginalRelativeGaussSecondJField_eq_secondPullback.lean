-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussSecondJField_eq_secondPullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:37:33.071876+00:00
-- url     : https://prove2.me/submissions/d243960f-720e-4e58-87f3-4736f84828c7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalFrickeLevelPullback_eq_hecke


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRelativeGaussSecondJField N p h4N hN hp =
      lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
        (Nat.mul_pos hN hp) (lpsOriginalRationalJElement N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalRationalFrickeLevelPullback_eq_hecke]
  rfl
end QEC.Coding.TannerLiftedProduct
