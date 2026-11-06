-- Prove2me | solution 1 for SatFree.inTime_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:46:51.659884+00:00
-- url     : https://prove2.me/submissions/5dbe4146-2da0-43d3-bc02-9dd9180bdf4a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_Order
import Definitions.Def_FreeCode_Random
import Definitions.Def_FreeCode_Behind
import Definitions.Def_FreeCode_Brute
import Definitions.Def_FreeCode_Tied
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Main
import Theorems.Thm_SatFree_bruteForce
import Theorems.Thm_FreeCode_decidesTM_mono
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_exists_pow_le


set_option autoImplicit false
section
section
open SatFree
open Groundwork FreeCode
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution (k : ℕ) {ε : ℝ≥0} (hε : 0 < ε) : InTime k (1 + ε) := by
  obtain ⟨M, hfin, h⟩ := bruteForce
  obtain ⟨c, hc⟩ := h k
  obtain ⟨C₁, hC₁⟩ := exists_pow_le c (ε := (ε : ℝ)) hε
  refine ⟨M, c * C₁, hfin, decidesTM_mono (fun n => Nat.le_floor ?_) hc⟩
  have h1 : (2 : ℝ) ^ (((1 + ε : ℝ≥0) : ℝ) * n) = (2 : ℝ) ^ ((ε : ℝ) * n) * (2 : ℝ) ^ n := by
    rw [← Real.rpow_natCast 2 n, ← Real.rpow_add two_pos]
    congr 1
    push_cast
    ring
  rw [h1]
  push_cast
  calc (c : ℝ) * ((n : ℝ) + 2) ^ c * (2 : ℝ) ^ n ≤ (c : ℝ) * (C₁ * (2 : ℝ) ^ ((ε : ℝ) * n)) * (2 : ℝ) ^ n := by
        have := hC₁ n
        gcongr
    _ = (c : ℝ) * C₁ * ((2 : ℝ) ^ ((ε : ℝ) * n) * (2 : ℝ) ^ n) := by ring
end SatFree
