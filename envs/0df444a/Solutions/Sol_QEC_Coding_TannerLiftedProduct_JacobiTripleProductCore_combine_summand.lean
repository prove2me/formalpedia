-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.combine_summand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:33.567215+00:00
-- url     : https://prove2.me/submissions/d206ddf4-ccc0-4a1a-8396-1b69ecc2bba6

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (A Q : R) (n k : ℕ) :
    qBinom Q n (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1) * Q ^ (k + 1).choose 2 +
    qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 =
    qBinom Q (n + 1) (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 := by
  show _ = (qBinom Q n k + Q ^ (k + 1) * qBinom Q n (k + 1)) * _ * _
  ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
