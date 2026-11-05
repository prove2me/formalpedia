-- Prove2me | solution 1 for PaddedDescent.inRateTM_of_padded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:48:31.843607+00:00
-- url     : https://prove2.me/submissions/d61a471b-43fd-4f4b-a48f-a405b81f36fc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_PadRate
import Theorems.Thm_PaddedDescent_inRateTM_of_padded_mul

set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}
namespace PaddedDescent
theorem _root_.solution (he : PolyT e) (hA : PolyT A) (C₀ : ℕ)
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
      e (enc φ) ≤ C₀ * (n / 2 ^ sOf n + 1) ∧ (A (enc φ, pad (e (enc φ))) = true ↔ Satisfiable φ)) : InRateTM (3 / 19) := by
  refine inRateTM_of_padded_mul he hA C₀ (fun n => C₀ * (n / 2 ^ sOf n + 1)) (fun n => ?_) h
  have h1 : n / 2 ^ sOf n * 2 ^ sOf n ≤ n := Nat.div_mul_le_self _ _
  calc C₀ * (n / 2 ^ sOf n + 1) * 2 ^ sOf n = C₀ * (n / 2 ^ sOf n * 2 ^ sOf n + 2 ^ sOf n) := by ring
    _ ≤ C₀ * (n + 2 ^ sOf n) := Nat.mul_le_mul_left _ (Nat.add_le_add_right h1 _)
end PaddedDescent
