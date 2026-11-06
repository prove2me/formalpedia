-- Prove2me | solution 1 for PiecesCounted.ite_cast_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:37.420278+00:00
-- url     : https://prove2.me/submissions/e1f62fa6-90d5-4fac-80ef-deba221be836

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Trimmed
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Assume

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution (n m : ℕ) : (if (n : ℤ) ≤ (m : ℤ) then (n : ℤ) else (m : ℤ)) = ((min n m : ℕ) : ℤ) := by
  by_cases h : n ≤ m
  · rw [if_pos (by exact_mod_cast h), min_eq_left h]
  · rw [if_neg (by exact_mod_cast h), min_eq_right (by omega)]
end PiecesCounted
