-- Prove2me | solution 1 for SplitSat.size_list_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:25:59.622245+00:00
-- url     : https://prove2.me/submissions/58c5b8b3-5541-40e5-aadf-208eaa2855bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_SplitSat_sum_size_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_sum_size_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_size_list
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.size_list



set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify
namespace SplitSat
theorem _root_.solution {α : Type} [HasSize α] {l : List α} {k s : ℕ} (hl : l.length ≤ k) (hs : ∀ x ∈ l, size x ≤ s) :
    size l ≤ k * (s + 1) + 1 := by
  rw [size_list]
  exact Nat.succ_le_succ ((sum_size_le l hs).trans (Nat.mul_le_mul_right _ hl))
end SplitSat
