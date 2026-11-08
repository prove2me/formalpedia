-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPSLList_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:32:48.511494+00:00
-- url     : https://prove2.me/submissions/0f5be784-ff68-4b4f-9b99-5d45fe0a8c9d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Mathlib.Data.List.FinRange
import Mathlib.Data.Quot
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_psl_two_zmod
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_747ca7d85c_18
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hqTwo : q ≠ 2) :
    (lpsPSLList q).length = q * (q ^ 2 - 1) / 2 := by
  have h := Fintype.card_congr (lpsPSLEnumerationEquiv q)
  simpa [card_psl_two_zmod q hqTwo] using h
end QEC.Coding.TannerLiftedProduct
