-- Prove2me | solution 1 for PaddedDescent.F.Mark.Layers.drop_eq_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:57:32.82593+00:00
-- url     : https://prove2.me/submissions/fe2795e7-5a86-467f-a27a-641b4075d30d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_PaddedDescent_F_MarkLayers
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open PaddedDescent.F.Mark.Layers
namespace PaddedDescent.F.Mark.Layers
theorem _root_.solution {Ls : List Fml} {i : ℕ} (hi : i < Ls.length) : Ls.drop i = Ls.getD i [] :: Ls.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
end PaddedDescent.F.Mark.Layers
