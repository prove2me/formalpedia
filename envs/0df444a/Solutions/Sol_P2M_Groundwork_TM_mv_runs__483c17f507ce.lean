-- Prove2me | solution 1 for P2M_Groundwork_TM_mv_runs__483c17f507ce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:47:51.970376+00:00
-- url     : https://prove2.me/submissions/47b99943-ae1c-4bc0-885c-0d92e2a8185a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Rename
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_TM_Move
import Theorems.Thm_Groundwork_TM_mv_runs
import Theorems.Thm_Groundwork_TM_code_mir
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_mirror_mirror
attribute [local simp] Groundwork.TM.length_mirror



set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
namespace Groundwork.TM
theorem _root_.solution {i j : Stk} (hij : i ≠ j) (hi : i ≠ .cnt) (hj : j ≠ .cnt) (x : V) {S : Stk → List Sym} {W : List Sym}
    (h : S i = mirror (code x) ++ W) :
    (mv i j).Runs none S ((code x).length + 1) (Function.update (Function.update S i W) j (code x ++ S j)) := by
  have r := mv_runs hij hi hj x.mir (S := S) (W := W) (by rw [code_mir]; exact h)
  rw [code_mir, mirror_mirror, length_mirror] at r
  exact r
end Groundwork.TM
