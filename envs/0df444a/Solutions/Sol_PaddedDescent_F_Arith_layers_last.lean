-- Prove2me | solution 1 for PaddedDescent.F.Arith.layers_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:22.61816+00:00
-- url     : https://prove2.me/submissions/5db17b13-561b-474a-b538-df41232dd3cb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {Δ s n : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (hn : 6 ≤ n) :
    2 ^ layersOf s * (Δ * n) + 5 * 3 ^ layersOf s ≤ 3 ^ layersOf s * (n + 2) := by
  obtain ⟨h, hh⟩ : ∃ h, h = betaOf s + 2 := ⟨_, rfl⟩
  have e : layersOf s = 2 * h := by rw [hh, layersOf]; ring
  have e2 : (2 : ℕ) ^ (2 * h) = 4 ^ h := by rw [pow_mul]; norm_num
  have e3 : (3 : ℕ) ^ (2 * h) = 9 ^ h := by rw [pow_mul]; norm_num
  have h2 : 2 * Δ ≤ 2 ^ h := by
    rw [hh, pow_add]; omega
  have h3 : 4 ^ h * 2 ^ h ≤ 9 ^ h := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) h
  have h4 : 2 * (4 ^ h * Δ) ≤ 9 ^ h := by
    calc 2 * (4 ^ h * Δ) = 4 ^ h * (2 * Δ) := by ring
      _ ≤ 4 ^ h * 2 ^ h := Nat.mul_le_mul_left _ h2
      _ ≤ 9 ^ h := h3
  rw [e, e2, e3]
  obtain ⟨A, hA⟩ : ∃ A, A = 9 ^ h := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = 4 ^ h * Δ := ⟨_, rfl⟩
  have e4 : 4 ^ h * (Δ * n) = D * n := by rw [hD]; ring
  rw [e4, ← hA]
  rw [← hD, ← hA] at h4
  nlinarith
end PaddedDescent.F.Arith
