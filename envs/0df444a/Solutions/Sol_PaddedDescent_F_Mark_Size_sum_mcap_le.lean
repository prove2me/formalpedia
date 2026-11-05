-- Prove2me | solution 1 for PaddedDescent.F.Mark.Size.sum_mcap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:11:31.142964+00:00
-- url     : https://prove2.me/submissions/c1032bd8-5cd8-4151-b789-02b6f835e4f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_PaddedDescent_F_Mark_Size_sum_length_tst_node_le
import Theorems.Thm_PaddedDescent_F_Mark_Size_mcap_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}
namespace PaddedDescent.F.Mark.Size
theorem _root_.solution {k w y β b : ℕ} (h0 : 0 < b) (h : adm k g n w Ls y = true) {a : ℕ} (ha : a < g) :
    ∑ a' ∈ (range g).erase a, mcap g n β b Ls y a a' ≤ 2 * (2 + β) * (tch g n Ls a).length := by
  calc ∑ a' ∈ (range g).erase a, mcap g n β b Ls y a a'
      ≤ ∑ a' ∈ (range g).erase a, (2 + β) * ∑ i ∈ range Ls.length, (tst g n Ls a a' i).length :=
        sum_le_sum fun a' ha' => mcap_le h0 h ha (mem_range.1 (mem_erase.1 ha').2) (mem_erase.1 ha').1.symm
    _ = (2 + β) * ∑ a' ∈ (range g).erase a, ∑ i ∈ range Ls.length, (tst g n Ls a a' i).length := by rw [mul_sum]
    _ ≤ (2 + β) * (2 * (tch g n Ls a).length) := Nat.mul_le_mul_left _ (sum_length_tst_node_le ha)
    _ = 2 * (2 + β) * (tch g n Ls a).length := by ring
end PaddedDescent.F.Mark.Size
