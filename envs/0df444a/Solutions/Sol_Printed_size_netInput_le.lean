-- Prove2me | solution 1 for Printed.size_netInput_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:21:48.775705+00:00
-- url     : https://prove2.me/submissions/de3fff9b-eb4f-43c7-aa2f-0cbda052ec12

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_Printed_size_listOfFn_le
import Theorems.Thm_Printed_c_le
import Theorems.Thm_Eight_SecNetworks_Net_c_le
import Theorems.Thm_Groundwork_SatNet_c_le
import Theorems.Thm_Printed_size_unary


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution {g : ℕ} (N : Net g) {P B : ℕ} (h : N.Is P B) : size (netInput N P B) ≤ (4 * g ^ 2 + 6 * g + 6) * (P + B) := by
  have hP := h.P_pos
  have s1 : size (List.ofFn fun a : Fin g => unary (N.len a)) ≤ g * (2 * P + 1 + 1) + 1 := size_listOfFn_le _ _ fun a => by
    have := h.len_le a
    rw [size_unary]
    omega
  have s2 : size (List.ofFn fun a : Fin g => List.ofFn fun b : Fin g => if a = b then [] else unary (N.c a b)) ≤ g * (g * (2 * P + 1 + 1) + 1 + 1) + 1 :=
    size_listOfFn_le _ _ fun a => size_listOfFn_le _ _ fun b => by
      by_cases hab : a = b
      · rw [if_pos hab]
        change 1 ≤ _
        omega
      · have := c_le h hab
        rw [if_neg hab, size_unary]
        omega
  have e : size (netInput N P B) = size (unary P) + size (unary B) + (size (List.ofFn fun a : Fin g => unary (N.len a)) +
      size (List.ofFn fun a : Fin g => List.ofFn fun b : Fin g => if a = b then [] else unary (N.c a b))) := rfl
  rw [e, size_unary, size_unary]
  have t1 : g * (2 * P + 1 + 1) ≤ g * (4 * (P + B)) := Nat.mul_le_mul_left _ (by omega)
  have t2 : g * (g * (2 * P + 1 + 1) + 1 + 1) ≤ g * (g * (4 * (P + B)) + 2 * (P + B)) := Nat.mul_le_mul_left _ (by omega)
  have t3 : (4 * g ^ 2 + 6 * g + 6) * (P + B) = g * (4 * (P + B)) + g * (g * (4 * (P + B)) + 2 * (P + B)) + 6 * (P + B) := by ring
  omega
end Printed
