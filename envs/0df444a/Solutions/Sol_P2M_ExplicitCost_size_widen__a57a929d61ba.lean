-- Prove2me | solution 1 for P2M_ExplicitCost_size_widen__a57a929d61ba
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:23:50.297607+00:00
-- url     : https://prove2.me/submissions/eb702c0e-6454-42fb-804c-0793e6a5e9d0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_ExplicitCost_size_widen
import Theorems.Thm_ExplicitCost_size_map_fst

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution (u : X0 NetInput × ℕ) : size (widen₁ K g u) ≤ size u + (2 * K + 2 * g + 2) := size_map_fst (fun c => (size_widen K g c).le) u
end ExplicitCost
