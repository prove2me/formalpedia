-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPSLIndexInv_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:32:53.990357+00:00
-- url     : https://prove2.me/submissions/df903f94-4776-4b15-9a01-629cac887dff

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Mathlib.Data.List.FinRange
import Mathlib.Data.Quot
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPSLIndexMul_decode
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPSLIndexInv_decode
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_747ca7d85c_18
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (i : Fin (lpsPSLList q).length) :
    lpsPSLIndexMul q (lpsPSLIndexInv q i) i = lpsPSLIndexOne q := by
  apply (lpsPSLEnumerationEquiv q).injective
  rw [lpsPSLIndexMul_decode, lpsPSLIndexInv_decode]
  simp [lpsPSLIndexOne]
end QEC.Coding.TannerLiftedProduct
