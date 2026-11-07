-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.extract_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:48:11.326892+00:00
-- url     : https://prove2.me/submissions/aed50ea0-ab0f-43df-9581-f25ed939fdef

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k ℓ : ℕ) :
    (-q ^ (2 * k + 1)) ^ ℓ = (-1) ^ ℓ * q ^ (ℓ * (2 * k + 1)) := by
  rw [show (-q ^ (2 * k + 1) : R) = (-1 : R) * q ^ (2 * k + 1) by ring_nf, mul_pow,
      show (q ^ (2 * k + 1)) ^ ℓ = q ^ (ℓ * (2 * k + 1)) by rw [← pow_mul]; ring_nf]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
