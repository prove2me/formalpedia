-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_last_factor_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:54:14.69271+00:00
-- url     : https://prove2.me/submissions/96a86984-d457-4a59-9175-42dfe37c2c1f

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (ℓ : ℕ) :
    (1 : R) - q ^ 2 * (q ^ 2) ^ ℓ = 1 - q ^ (2 * (↑ℓ + 1)) := by
  rw [show 2 * (ℓ + 1) = 2 + 2 * ℓ by omega, pow_add, pow_mul]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
