-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSQuaternion.conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:26:58.386999+00:00
-- url     : https://prove2.me/submissions/6fc0fd82-e40e-4031-91fe-84be94ad3b16

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.TransferInstance
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRing

set_option autoImplicit false
open scoped MatrixGroups Quaternion
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
namespace LPSQuaternion
theorem _root_.solution (t u : LPSQuaternion) :
    (t * u).conj = u.conj * t.conj := by
  apply LPSQuaternion.ringEquivQuaternion.injective
  rw [LPSQuaternion.ringEquivQuaternion_conj, map_mul, star_mul,
    ← LPSQuaternion.ringEquivQuaternion_conj,
    ← LPSQuaternion.ringEquivQuaternion_conj, map_mul]
end LPSQuaternion
end QEC.Coding.TannerLiftedProduct
