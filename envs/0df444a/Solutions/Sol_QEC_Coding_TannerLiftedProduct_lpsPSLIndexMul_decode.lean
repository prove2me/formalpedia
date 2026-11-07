-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPSLIndexMul_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:54:43.652235+00:00
-- url     : https://prove2.me/submissions/42781cba-a17e-4124-aeed-593499ef85d8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Mathlib.Data.List.FinRange
import Mathlib.Data.Quot
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_747ca7d85c_18
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (i j : Fin (lpsPSLList q).length) :
    (lpsPSLEnumerationEquiv q) (lpsPSLIndexMul q i j) =
      (lpsPSLEnumerationEquiv q) i * (lpsPSLEnumerationEquiv q) j := by
  simp [lpsPSLIndexMul]
end QEC.Coding.TannerLiftedProduct
