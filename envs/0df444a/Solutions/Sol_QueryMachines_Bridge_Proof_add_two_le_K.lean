-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.add_two_le_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:58:49.964261+00:00
-- url     : https://prove2.me/submissions/d78a9bfe-dd10-44c4-829f-87a203d1838f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_CountedToPadded_Pick

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} (hL : Levels K e C₀) : ∀ l : ℕ, l + 2 ≤ K l
  | 0 => hL.K_two 0
  | l + 1 => by have := solution hL l; have := hL.K_lt l; omega
end QueryMachines.Bridge.Proof
