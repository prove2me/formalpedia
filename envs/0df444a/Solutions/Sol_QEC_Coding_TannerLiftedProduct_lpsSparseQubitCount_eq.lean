-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsSparseQubitCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:17:22.932455+00:00
-- url     : https://prove2.me/submissions/6c2bb10b-7609-4395-9d4b-d98011c803df

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {q D r r' : ℕ} [Fact q.Prime] :
    D * (D * (lpsPSLList q).length) + (2 * r) * ((2 * r') * (lpsPSLList q).length) =
      (lpsPSLList q).length * (D ^ 2 + 4 * r * r') := by ring
end QEC.Coding.TannerLiftedProduct
