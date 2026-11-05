-- Prove2me | solution 1 for PaddedDescent.F.Mark.Size.mu_le_of_adm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:55:07.790612+00:00
-- url     : https://prove2.me/submissions/5565d2b0-c7fa-49bb-8636-d3341db888d4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_PaddedDescent_F_Mark_Size_mu_comm
import Theorems.Thm_PaddedDescent_F_Mark_Size_tst_comm
import Theorems.Thm_PaddedDescent_F_Mark_Size_adm_iff
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}
namespace PaddedDescent.F.Mark.Size
theorem _root_.solution {k w y : ℕ} (h : adm k g n w Ls y = true) {a a' i : ℕ} (ha : a < g) (ha' : a' < g) (hne : a ≠ a') (hi : i < Ls.length) :
    mu g Ls y a a' i ≤ (tst g n Ls a a' i).length := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ((adm_iff.1 h i hi).2.2 a ha a' ha').2 hlt
  · rw [mu_comm, tst_comm]; exact ((adm_iff.1 h i hi).2.2 a' ha' a ha).2 hgt
end PaddedDescent.F.Mark.Size
