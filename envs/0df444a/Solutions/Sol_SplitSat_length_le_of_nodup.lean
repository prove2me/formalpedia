-- Prove2me | solution 1 for SplitSat.length_le_of_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:23:31.169191+00:00
-- url     : https://prove2.me/submissions/1073be9f-fabd-4a77-93da-04a2a09dedc4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_Groundwork_DecodeK_IsKCNF_length_le
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Sat3_Is3CNF_length_le
import Theorems.Thm_SplitSat_exists_instance
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify
namespace SplitSat
theorem _root_.solution {k n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (hnd : ψ.Nodup) :
    ψ.length ≤ 2 ^ k * (n + 2) ^ k := by
  obtain ⟨φ, h3, rfl⟩ := exists_instance hψ hnd
  rw [Decode.length_toN]
  calc φ.length ≤ (2 * n + 1) ^ k := DecodeK.IsKCNF.length_le h3
    _ ≤ (2 * (n + 2)) ^ k := Nat.pow_le_pow_left (by omega) k
    _ = 2 ^ k * (n + 2) ^ k := mul_pow _ _ _
end SplitSat
