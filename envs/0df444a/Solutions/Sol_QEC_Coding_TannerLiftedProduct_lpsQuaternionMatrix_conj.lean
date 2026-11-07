-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionMatrix_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:33:19.316301+00:00
-- url     : https://prove2.me/submissions/20e1ad13-73f8-40e6-b579-358378f680f7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open QEC.Coding.BalancedProduct.LPSArithmetic
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q : ℕ) [Fact q.Prime] (t : LPSQuaternion) :
    lpsQuaternionMatrix q t.conj = (lpsQuaternionMatrix q t).adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lpsQuaternionMatrix, Matrix.adjugate_fin_two] <;> ring
end QEC.Coding.TannerLiftedProduct
