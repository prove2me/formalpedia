-- Prove2me | solution 1 for Printed.eStar_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:16:37.47272+00:00
-- url     : https://prove2.me/submissions/91c51523-cac4-4f86-9772-799089b7916c

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
import Theorems.Thm_Printed_nonneg_of_mem

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
namespace Printed
theorem _root_.solution {e : ℝ} (h : ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e) : eStar ≤ e := csInf_le ⟨0, fun _ he => nonneg_of_mem he⟩ h
end Printed
