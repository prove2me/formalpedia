-- Prove2me | solution 1 for PaddedDescent.F.Mark.Pi.layer_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:25:05.623832+00:00
-- url     : https://prove2.me/submissions/9ead9717-e012-4cd9-95e0-b644af463028

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]
namespace PaddedDescent.F.Mark.Pi
theorem _root_.solution (Ls : List Fml) {e : ℕ} (he : e < (cls Ls).length) : (clAt Ls e).1 < Ls.length := by
  have hm : clAt Ls e ∈ cls Ls := by
    rw [clAt, List.getD_eq_getElem _ _ he]
    exact List.getElem_mem he
  obtain ⟨i, hi, hq⟩ := List.mem_flatMap.1 hm
  obtain ⟨C, -, hC⟩ := List.mem_map.1 hq
  rw [← hC]
  exact List.mem_range.1 hi
end PaddedDescent.F.Mark.Pi
