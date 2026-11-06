-- Prove2me | solution 1 for Sat3Graph.numFresh_append_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:52:23.099191+00:00
-- url     : https://prove2.me/submissions/054f6759-6d86-4fc3-b894-4c73ef043034

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Split
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_GraphProblems_Color
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Coloring
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Sat3Graph_numFresh_append
import Theorems.Thm_Sat3Graph_numFresh_eq_zero
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SplitSat
namespace Sat3Graph
theorem _root_.solution {x y : Fml} {m : ℕ} (hx : numFresh x ≤ m) (hy : ∀ C ∈ y, C.length ≤ 3) : numFresh (x ++ y) ≤ m := by
  rw [numFresh_append, numFresh_eq_zero hy]
  exact hx
end Sat3Graph
