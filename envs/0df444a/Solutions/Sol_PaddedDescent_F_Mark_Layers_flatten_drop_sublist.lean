-- Prove2me | solution 1 for PaddedDescent.F.Mark.Layers.flatten_drop_sublist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:49:33.7322+00:00
-- url     : https://prove2.me/submissions/6e55a576-7f9d-43e9-ac4c-5c5f3b910a74

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

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open PaddedDescent.F.Mark.Layers
namespace PaddedDescent.F.Mark.Layers
theorem _root_.solution (Ls : List Fml) (i : ℕ) : (Ls.drop i).flatten.Sublist Ls.flatten :=
  (List.drop_sublist i Ls).flatten
end PaddedDescent.F.Mark.Layers
