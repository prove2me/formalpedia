-- Prove2me | solution 1 for PaddedDescent.two_pow_sOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:35:00.495196+00:00
-- url     : https://prove2.me/submissions/2dda34c3-479f-406c-bbe9-3c1ccc9ce806

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_PadRate

set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
namespace PaddedDescent
theorem _root_.solution (n : ℕ) : 2 ^ sOf n ≤ Nat.log2 (n + 2) := by
  have hmono : Nat.log2 n ≤ Nat.log2 (n + 2) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  have hs : sOf n ≤ Nat.log2 (Nat.log2 n) := by unfold sOf; omega
  by_cases h0 : Nat.log2 n = 0
  · have : sOf n = 0 := by
      have : Nat.log2 (Nat.log2 n) = 0 := by rw [h0]; rfl
      omega
    rw [this]
    exact (Nat.le_log2 (by omega)).2 (by omega)
  · calc 2 ^ sOf n ≤ 2 ^ Nat.log2 (Nat.log2 n) := Nat.pow_le_pow_right (by norm_num) hs
      _ ≤ Nat.log2 n := Nat.log2_self_le h0
      _ ≤ _ := hmono
end PaddedDescent
