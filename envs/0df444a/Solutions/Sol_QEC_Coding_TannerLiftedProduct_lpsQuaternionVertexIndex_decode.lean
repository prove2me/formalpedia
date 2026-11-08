-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuaternionVertexIndex_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:32:52.341202+00:00
-- url     : https://prove2.me/submissions/674d2705-ade9-4f4f-ab78-36eaf8a627bc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Mathlib.Data.List.FinRange
import Mathlib.Data.Quot
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionPSL_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_747ca7d85c_18
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ} (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    (lpsPSLEnumerationEquiv a.q) (lpsQuaternionVertexIndex a t ht) =
      lpsQuaternionPSL a t ht := by
  simp [lpsQuaternionVertexIndex, lpsEffectiveQuaternionPSL_eq]
end QEC.Coding.TannerLiftedProduct
