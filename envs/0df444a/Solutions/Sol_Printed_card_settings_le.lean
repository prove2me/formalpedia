-- Prove2me | solution 1 for Printed.card_settings_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:14.460208+00:00
-- url     : https://prove2.me/submissions/483fa132-7b6d-4cde-8125-cf2772518949

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry
import Theorems.Thm_Groundwork_card_tuples
import Theorems.Thm_Groundwork_card_words
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
variable {C : Type} [HasSize C] {g K : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]
namespace Printed
theorem _root_.solution (h : N.Is P B) (hK0 : 0 < K) (x : ℕ) (γ : Fin K) (hG1 : K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) :
    #(tuples (fun a => Paper.grouping hK0 x a = γ) N.S []) ≤ 2 ^ (P * (2 * g / K)) := by
  rw [card_tuples]
  calc ∏ a with Paper.grouping hK0 x a = γ, #(N.S a) ≤ ∏ a with Paper.grouping hK0 x a = γ, 2 ^ P := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun a _ =>
        calc #(N.S a) ≤ #(words (N.len a)) := card_le_card fun z hz => mem_words.2 (h.len_S a z hz)
          _ = 2 ^ N.len a := card_words _
          _ ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) (h.len_le a)
    _ = (2 ^ P) ^ #{a : Fin g | Paper.grouping hK0 x a = γ} := Finset.prod_const _
    _ ≤ (2 ^ P) ^ (2 * g / K) := Nat.pow_le_pow_right Nat.one_le_two_pow (by
        rw [Nat.le_div_iff_mul_le hK0, Nat.mul_comm]
        exact hG1)
    _ = 2 ^ (P * (2 * g / K)) := (pow_mul 2 P _).symm
end Printed
