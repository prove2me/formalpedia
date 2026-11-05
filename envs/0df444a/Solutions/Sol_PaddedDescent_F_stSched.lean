-- Prove2me | solution 1 for PaddedDescent.F.stSched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:10:54.210116+00:00
-- url     : https://prove2.me/submissions/6529d0de-32b1-45ab-b406-37337875a325

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithCol
import Definitions.Def_PaddedDescent_F_ArithSched
import Theorems.Thm_PaddedDescent_F_Arith_schedState_succ
import Theorems.Thm_PaddedDescent_F_Arith_len_schedState_le
import Theorems.Thm_PaddedDescent_F_Arith_schedLen_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_cap_eq
import Theorems.Thm_PaddedDescent_Kseq_zero__d4a598


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork PaddedDescent.F.Lists
open Arith
namespace PaddedDescent.F
theorem _root_.solution : StSched := by
  intro pad t ht
  have key : ∀ j ≤ t, (List.replicate j ()).foldl
      (fun st _ => cap pad ([], [], []) ((st.2.1, mulU st.2.1 st.2.2) :: st.1, sqU (mulU st.2.1 st.2.2), st.2.2 ++ st.2.2))
      (cap pad ([], [], []) ([], List.replicate 256 (), List.replicate (Lseq 0) ())) = schedState j := by
    intro j
    induction j with
    | zero =>
      intro _
      have e : (([], List.replicate 256 (), List.replicate (Lseq 0) ()) : List Lvl × U × U) = schedState 0 := by
        rw [schedState, schedL, Kseq_zero]
      rw [List.replicate_zero, List.foldl_nil, e]
      exact cap_eq ((len_schedState_le 0).trans ((schedLen_mono (Nat.zero_le t)).trans ht))
    | succ j ih =>
      intro hj
      rw [List.replicate_succ' (n := j), List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil, schedState_succ]
      exact cap_eq ((len_schedState_le (j + 1)).trans ((schedLen_mono hj).trans ht))
  exact key t le_rfl
end PaddedDescent.F
