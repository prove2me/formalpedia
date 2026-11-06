-- Prove2me | solution 1 for Printed.half_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:08:16.181579+00:00
-- url     : https://prove2.me/submissions/b7ab548c-1524-4709-a435-dd49397b2849

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
import Theorems.Thm_Printed_achievable_half
import Theorems.Thm_Paper_achievable_half


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
namespace Printed
theorem _root_.solution : (1 / 2 : ℝ) ∈ {e : ℝ | ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e} :=
  fun K₀ => ⟨max K₀ 2, le_max_left _ _, achievable_half (le_max_right _ _)⟩
end Printed
