-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exponent_identity_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:39:49.815715+00:00
-- url     : https://prove2.me/submissions/815f4c68-e1b5-46f9-8c6c-b4c266779bb5

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ : ℕ) :
    (↑ℓ - (↑j + 1 : ℤ)) ^ 2 + ↑ℓ =
    (↑j + 1) ^ 2 + 2 * ↑(ℓ.choose 2) - 2 * ↑j * ↑ℓ := by
  rcases eq_or_lt_of_le (Nat.zero_le ℓ) with rfl | hge
  · simp [Nat.choose_two_right]
    ring
  · have h : ℓ * (ℓ - 1) = 2 * ℓ.choose 2 := by
      have := Nat.choose_two_right ℓ
      have : 2 ∣ ℓ * (ℓ - 1) := by
        rcases Nat.even_or_odd ℓ with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp [hk] <;> ring_nf <;> omega
      omega
    zify [hge] at h
    nlinarith
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
