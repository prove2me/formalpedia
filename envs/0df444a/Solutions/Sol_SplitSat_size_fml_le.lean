-- Prove2me | solution 1 for SplitSat.size_fml_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:37:23.509436+00:00
-- url     : https://prove2.me/submissions/9abbffcc-67e0-46e7-b183-97134b3c7fc0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_SplitSat_size_list_le
import Theorems.Thm_SplitSat_size_lit_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_size_list_le
import Theorems.Thm_Groundwork_Prog_size_lit_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify
namespace SplitSat
theorem _root_.solution {k : ℕ} {x : Fml} {m n : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    size x ≤ m * (k * (n + 2 + 1) + 1 + 1) + 1 :=
  size_list_le hm fun C hC => size_list_le (hx C hC).1 fun l hl => size_lit_le ((hx C hC).2 l hl)
end SplitSat
