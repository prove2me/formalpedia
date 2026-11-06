-- Prove2me | solution 1 for PairsToBound.length_le_widthOr3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:58:47.970982+00:00
-- url     : https://prove2.me/submissions/e91ecc13-1693-49c2-8f06-2931a24a9090

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Width
import Theorems.Thm_PairsToBound_mem_le_foldr_max
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PairsToBound
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution {n : ℕ} {φ : CNF n} {C : List (Sat3.Lit n)} (h : C ∈ φ) : C.length ≤ widthOr3 φ :=
  mem_le_foldr_max (List.mem_map_of_mem h)
end PairsToBound
