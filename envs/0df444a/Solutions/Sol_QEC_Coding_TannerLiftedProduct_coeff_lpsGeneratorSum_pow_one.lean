-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_lpsGeneratorSum_pow_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:43:02.357071+00:00
-- url     : https://prove2.me/submissions/0c1fd9b5-761f-4793-aa25-cc2ea3fafe00

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
import Mathlib.Data.Fintype.Vector
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_cayleyGeneratorSum_pow

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v} [Group G] [Fintype W]
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : LPSResiduePrime p) (n : ℕ) :
    (cayleyGeneratorSum (lpsQuaternionLabel a) ^ n).coeff 1 =
      ((lpsClosedWords a n).card : ℂ) := by
  rw [coeff_cayleyGeneratorSum_pow]
  congr 1
end QEC.Coding.TannerLiftedProduct
