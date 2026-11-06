-- Prove2me | solution 1 for Printed.achievable_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:57:14.486303+00:00
-- url     : https://prove2.me/submissions/e5d202ac-ca45-463c-a03a-a303262accd1

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
import Theorems.Thm_Printed_bruteMachine_poly
import Theorems.Thm_Printed_bruteMachine_achieves

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
namespace Printed
theorem _root_.solution {K : ℕ} (hK : 2 ≤ K) : Achievable K (1 / 2) :=
  have ⟨Cc, h⟩ := bruteMachine_achieves K hK
  ⟨hK, by norm_num, bruteMachine K, Cc, bruteMachine_poly K, h⟩
end Printed
