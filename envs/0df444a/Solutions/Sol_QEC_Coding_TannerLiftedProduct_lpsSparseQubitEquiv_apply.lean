-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsSparseQubitEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:13:02.93812+00:00
-- url     : https://prove2.me/submissions/b8c8f3ed-6707-4c1e-97f8-785291a9aaf2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {q D r r' : ℕ} [Fact q.Prime]
    (qubit : LPSSparseQubitIndex q D r r') :
    lpsSparseQubitEquiv qubit = lpsSparseQubitDecode qubit := by cases qubit <;> rfl
end QEC.Coding.TannerLiftedProduct
