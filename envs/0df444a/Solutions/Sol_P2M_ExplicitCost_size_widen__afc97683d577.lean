-- Prove2me | solution 1 for P2M_ExplicitCost_size_widen__afc97683d577
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:32:25.889981+00:00
-- url     : https://prove2.me/submissions/765dd0f0-7ba6-43d0-9af1-bc023c7bba84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_size_map_fst
import Theorems.Thm_P2M_ExplicitCost_size_widen__a57a929d61ba

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution (u : (X0 NetInput × ℕ) × ℕ) : size (widen₂ K g u) ≤ size u + (2 * K + 2 * g + 2) := size_map_fst (size_widen₁ K g) u
end ExplicitCost
