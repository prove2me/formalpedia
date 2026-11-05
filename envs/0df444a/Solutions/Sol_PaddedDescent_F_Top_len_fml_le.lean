-- Prove2me | solution 1 for PaddedDescent.F.Top.len_fml_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:38:54.390727+00:00
-- url     : https://prove2.me/submissions/6ec8b7de-e809-4e08-96ef-da0f9103a090

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_NSat
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_PaddedDescent_F_Top_len_list_le
import Theorems.Thm_PaddedDescent_F_Top_len_lit_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Top
open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)
namespace PaddedDescent.F.Top
theorem _root_.solution {x : Fml} {k m n : ℕ} (hm : x.length ≤ m) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    len x ≤ m * (k * (3 * n + 5) + 10) + 2 := by
  refine len_list_le hm (s := k * (3 * n + 5) + 8) fun C hC => ?_
  have h := len_list_le (hx C hC).1 fun l hl => len_lit_le ((hx C hC).2 l hl)
  have e : 3 * n + 3 + 2 = 3 * n + 5 := rfl
  rw [e] at h
  omega
end PaddedDescent.F.Top
