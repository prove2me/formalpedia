-- Prove2me | solution 1 for PaddedDescent.F.Top.walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:32:43.10389+00:00
-- url     : https://prove2.me/submissions/2f874acd-324b-4709-934d-2819c856a135

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
import Theorems.Thm_PaddedDescent_F_Top_foldl_capped_eq_iterate
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Sparsify_roundB_iterate_of_le
import Theorems.Thm_PaddedDescent_F_cap_eq
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
theorem _root_.solution : StWalk := by
  intro k pad τ test r d hd hlen hst
  unfold walkF
  rw [foldl_capped_eq_iterate (cap pad ([], false)) (roundB (stepK (theta τ) k) test) (fun x => len x ≤ pad.length)
    (fun x hx => cap_eq hx) pad ([r], false) (fun i _ => hst i),
    Sparsify.roundB_iterate_of_le (stepK (theta τ) k) test d r hd pad.length (by omega)]
end PaddedDescent.F.Top
