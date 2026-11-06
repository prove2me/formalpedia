-- Prove2me | solution 1 for Sat3Graph.numFresh_dedup_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:35:17.832324+00:00
-- url     : https://prove2.me/submissions/f1e8a148-58fc-470a-ba61-a2c13ee3c562

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_General
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Split
import Theorems.Thm_Eight_Width_numFresh_cons
import Theorems.Thm_Groundwork_PolyT_dedup
attribute [local fun_prop] Groundwork.PolyT.dedup



set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Eight.Width
namespace Sat3Graph
theorem _root_.solution : ∀ x : Fml, numFresh x.dedup ≤ numFresh x
  | [] => le_rfl
  | C :: x => by
    have ih := solution x
    by_cases h : C ∈ x
    · rw [List.dedup_cons_of_mem h, numFresh_cons]
      omega
    · rw [List.dedup_cons_of_notMem h, numFresh_cons, numFresh_cons]
      omega
end Sat3Graph
