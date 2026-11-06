-- Prove2me | solution 1 for Printed.threeSat_by_algorithm_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:14:18.286116+00:00
-- url     : https://prove2.me/submissions/a963051d-193a-4d36-a175-116d9cc1890f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Proof
import Theorems.Thm_Paper_steps_to_time


set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Eight Eight.SecNetworks Paper QueryMachines
namespace Printed
theorem _root_.solution (h : StDecides) : Sat3.ThmEveryDelta := fun δ hδ =>
  have ⟨_, _, hp, hd⟩ := h (δ / 2) (by linarith)
  steps_to_time hδ _ hp hd
end Printed
