-- Prove2me | solution 1 for SplitCount.leaf_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:41:08.12839+00:00
-- url     : https://prove2.me/submissions/4fd017b3-1da9-48ad-abc3-9c2a7136ad29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Width
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Leaf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_SatTopK_size_fml_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SplitCount_size_fml_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight.Width Occ
namespace SplitCount
theorem _root_.solution {q Bl n M m n₃ : ℕ} {Ψ₃ : Fml} (hn : n ≤ M) (h1 : 1 ≤ M) (hm : m ≤ Bl * n) (g1 : ∀ C ∈ Ψ₃, C.length ≤ 3) (g2 : Below n₃ Ψ₃)
    (g4 : n₃ ≤ n + q * m) (g5 : Ψ₃.length ≤ m + 3 * (q * m)) :
    n₃ + size Ψ₃ + 1 ≤ ((1 + q * Bl) + (1 + 3 * q) * Bl * (3 * (1 + q * Bl) + 11) + 2) * M ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a, a = 1 + q * Bl := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (1 + 3 * q) * Bl := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have hmM : m ≤ Bl * M := hm.trans (Nat.mul_le_mul_left _ hn)
  have hqm : q * m ≤ q * (Bl * M) := Nat.mul_le_mul_left _ hmM
  have e1 : n₃ ≤ a * M := by
    have : a * M = M + q * (Bl * M) := by rw [ha]; ring
    omega
  have e2 : Ψ₃.length ≤ b * M := by
    have : b * M = Bl * M + 3 * (q * (Bl * M)) := by rw [hb]; ring
    omega
  have e3 : 3 * (n₃ + 2 + 1) + 1 + 1 ≤ (3 * a + 11) * M := by
    have : (3 * a + 11) * M = 3 * (a * M) + 11 * M := by ring
    omega
  have e4 : size Ψ₃ ≤ b * M * ((3 * a + 11) * M) + 1 :=
    (size_fml_le (k := 3) e2 fun C hC => ⟨g1 C hC, g2 C hC⟩).trans (Nat.succ_le_succ (Nat.mul_le_mul_left _ e3))
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) M
  have h1M2 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ h1
  have e5 : a * M ≤ a * M ^ 2 := Nat.mul_le_mul_left _ hM2
  have e6 : b * M * ((3 * a + 11) * M) = b * (3 * a + 11) * M ^ 2 := by ring
  have e7 : (a + b * (3 * a + 11) + 2) * M ^ 2 = a * M ^ 2 + b * (3 * a + 11) * M ^ 2 + 2 * M ^ 2 := by ring
  omega
end SplitCount
