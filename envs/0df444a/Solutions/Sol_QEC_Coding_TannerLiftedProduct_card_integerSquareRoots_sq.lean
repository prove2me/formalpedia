-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_integerSquareRoots_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:36:55.426886+00:00
-- url     : https://prove2.me/submissions/b94f5288-d6cc-4547-96e4-587190b28dee

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerSquareRoots_sq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0 < m) :
    (integerSquareRoots (m ^ 2)).card = 2 := by
  rw [integerSquareRoots_sq m]
  simp [hm.ne']
end QEC.Coding.TannerLiftedProduct
