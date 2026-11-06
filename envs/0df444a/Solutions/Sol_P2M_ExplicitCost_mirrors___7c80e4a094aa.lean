-- Prove2me | solution 1 for P2M_ExplicitCost_mirrors___7c80e4a094aa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:22:14.082777+00:00
-- url     : https://prove2.me/submissions/ff942d0b-24f0-406e-a365-684c02e32b60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_size_widenC
import Theorems.Thm_ExplicitCost_size_map_fst
import Theorems.Thm_ExplicitCost_mirrors_query
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution : Mirrors asked.Ψ askedData.Ψ (Prod.map (widenC K g) id) (2 * K + 2 * g + 2) :=
  mirrors_query (fun _ => rfl) (size_map_fst fun c => (size_widenC K g c).le)
end ExplicitCost
