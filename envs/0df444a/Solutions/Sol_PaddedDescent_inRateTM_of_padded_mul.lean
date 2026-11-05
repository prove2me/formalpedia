-- Prove2me | solution 1 for PaddedDescent.inRateTM_of_padded_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:45:38.913606+00:00
-- url     : https://prove2.me/submissions/fefe4f30-13b9-4831-9a51-e53d8d4dab39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_PadRate
import Theorems.Thm_PaddedDescent_two_pow_sOf_le
import Theorems.Thm_PaddedDescent_padded_time_le
import Theorems.Thm_PaddedDescent_decidesTM_of_padded
import Theorems.Thm_Sat3_inRateTM_of_mulForm


set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}
namespace PaddedDescent
theorem _root_.solution (he : PolyT e) (hA : PolyT A) (C₀ : ℕ) (E : ℕ → ℕ)
    (hE : ∀ n, E n * 2 ^ sOf n ≤ C₀ * (n + 2 ^ sOf n))
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
      e (enc φ) ≤ E n ∧ (A (enc φ, pad (e (enc φ))) = true ↔ Satisfiable φ)) : InRateTM (3 / 19) := by
  obtain ⟨N, q, hfin, hN⟩ := decidesTM_of_padded he hA
  exact inRateTM_of_mulForm N hfin q (q * (C₀ + 42)) _ (fun n => q * (E n + 4 * Nat.log2 (n + 2) + 10)) (hN E h)
    (fun n => (padded_time_le q C₀ (two_pow_sOf_le n) (hE n)).1) fun n => (padded_time_le q C₀ (two_pow_sOf_le n) (hE n)).2
end PaddedDescent
