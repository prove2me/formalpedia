-- Prove2me | solution 1 for Printed.nonneg_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:03:15.225239+00:00
-- url     : https://prove2.me/submissions/28b0bb26-208b-42e8-8531-11882dc553ad

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Absorb
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic
import Definitions.Def_Printed_Achievable

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
namespace Printed
theorem _root_.solution {e : ℝ} (h : e ∈ {e : ℝ | ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e}) : 0 ≤ e :=
  have ⟨_, _, hA⟩ := h 0
  hA.2.1
end Printed
