-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.den_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:57:06.540799+00:00
-- url     : https://prove2.me/submissions/3bebae9a-16a1-4315-a328-a653f24bfe23

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_CountedToPadded_Need
import Theorems.Thm_QueryMachines_Bridge_Proof_e_pos

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork PaddedDescent.F Printed CliqueLevels
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} {num : U × U → ℕ × ℕ} (hL : Levels K e C₀) (hN : NumberBetween K e num) (l : ℕ) : 0 < (num (unary l, unary (K l))).2 := by
  rcases Nat.eq_zero_or_pos (num (unary l, unary (K l))).2 with h | h
  · have h1 := (hN.2 l).1
    rw [h, Nat.cast_zero, div_zero] at h1
    exact absurd (e_pos hL l) (not_lt.2 h1)
  · exact h
end QueryMachines.Bridge.Proof
