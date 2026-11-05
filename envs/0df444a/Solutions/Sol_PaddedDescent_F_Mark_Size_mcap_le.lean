-- Prove2me | solution 1 for PaddedDescent.F.Mark.Size.mcap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:05.961817+00:00
-- url     : https://prove2.me/submissions/8b59d117-249b-4dd5-9e36-a42884df7174

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_PaddedDescent_F_Mark_Size_sum_map_range
import Theorems.Thm_PaddedDescent_F_Mark_Size_ceil_le
import Theorems.Thm_PaddedDescent_F_Mark_Size_mu_le_of_adm
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Stepped_sum_map_range
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}
namespace PaddedDescent.F.Mark.Size
theorem _root_.solution {k w y β b : ℕ} (h0 : 0 < b) (h : adm k g n w Ls y = true) {a a' : ℕ} (ha : a < g) (ha' : a' < g) (hne : a ≠ a') :
    mcap g n β b Ls y a a' ≤ (2 + β) * ∑ i ∈ range Ls.length, (tst g n Ls a a' i).length := by
  rw [mcap, sum_map_range, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have h1 := mu_le_of_adm h ha ha' hne (mem_range.1 hi)
  have h2 := ceil_le h0 (tst g n Ls a a' i).length
  calc mu g Ls y a a' i * (1 + β) + ((tst g n Ls a a' i).length + b - 1) / b
      ≤ (tst g n Ls a a' i).length * (1 + β) + (tst g n Ls a a' i).length := Nat.add_le_add (Nat.mul_le_mul_right _ h1) h2
    _ = (2 + β) * (tst g n Ls a a' i).length := by ring
end PaddedDescent.F.Mark.Size
