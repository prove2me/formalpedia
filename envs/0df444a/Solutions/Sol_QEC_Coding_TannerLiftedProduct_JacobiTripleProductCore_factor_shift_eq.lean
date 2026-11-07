-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factor_shift_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:54.491784+00:00
-- url     : https://prove2.me/submissions/8c940bf0-879a-4e37-9c70-2a17a5b0bf58

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (n k : ℕ) :
    (1 : R) - q ^ 2 * (q ^ 2) ^ (n + k) = 1 - (q ^ 2 * (q ^ 2) ^ k) * (q ^ 2) ^ n := by ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
