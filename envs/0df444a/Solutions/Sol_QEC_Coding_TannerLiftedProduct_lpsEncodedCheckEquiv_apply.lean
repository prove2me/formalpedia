-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEncodedCheckEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:14:29.319721+00:00
-- url     : https://prove2.me/submissions/a8c78093-9a52-4ab8-9268-dd47dc5652df

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_113
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {q D r r' s : ℕ} [Fact q.Prime] {F : Type}
    (e : Fin s ≃ F) (c : LPSEncodedCheckIndex q D r r' s) :
    lpsEncodedCheckEquiv e c = lpsEncodedCheckDecode e c := by cases c <;> rfl
end QEC.Coding.TannerLiftedProduct
