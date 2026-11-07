-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exponent_simp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:10:49.316497+00:00
-- url     : https://prove2.me/submissions/abdf7414-c57c-42e4-95d6-90ce5a8d0a2d

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (k : ℕ) :
    (-(-x * q)) ^ k * (q ^ 2) ^ k.choose 2 = q ^ (k ^ 2) * x ^ k := by
  have h1 : k + 2 * k.choose 2 = k ^ 2 := by
    have : 2 ∣ k * (k - 1) := by
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩ <;> simp [hm] <;> ring_nf <;> omega
    rw [Nat.choose_two_right, Nat.mul_div_cancel' this]
    rcases k with _ | n
    · simp [sq]
    · simp [sq]
      ring
  rw [show (-(-x * q)) ^ k = (x * q) ^ k by simp [neg_neg], mul_pow,
      show (q ^ 2) ^ k.choose 2 = q ^ (2 * k.choose 2) by rw [← pow_mul],
      mul_assoc, ← pow_add, h1]
  ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
