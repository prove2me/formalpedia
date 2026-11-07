-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:49:56.277198+00:00
-- url     : https://prove2.me/submissions/511d55a1-c466-4106-8abc-f78fcce33ad8

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k ℓ : ℕ) :
    (-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 =
    q ^ (ℓ ^ 2) * (-(q ^ (1 + 2 * k))) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by
  have : ℓ ^ 2 + (1 + 2 * k) * ℓ = ℓ ^ 2 + ℓ + 2 * k * ℓ := by nlinarith
  have : (q : R) ^ (ℓ ^ 2) * (-(q : R) ^ (1 + 2 * k)) ^ ℓ =
      (-1 : R) ^ ℓ * (q : R) ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) := by rw [← this]; ring
  simp_all
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
