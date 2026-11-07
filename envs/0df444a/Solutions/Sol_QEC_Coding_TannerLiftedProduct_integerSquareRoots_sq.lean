-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.integerSquareRoots_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:35:53.046166+00:00
-- url     : https://prove2.me/submissions/e6d1a799-4728-4c0a-b475-d17430f4930f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) :
    integerSquareRoots (m ^ 2) = {(m : ℤ), -(m : ℤ)} := by
  ext z
  rw [mem_integerSquareRoots_iff]
  push_cast
  rw [sq_eq_sq_iff_eq_or_eq_neg]
  simp
end QEC.Coding.TannerLiftedProduct
