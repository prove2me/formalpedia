-- Prove2me | solution 1 for PaddedDescent.F.Mark.Prof.place_dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:11:02.802114+00:00
-- url     : https://prove2.me/submissions/50992d07-bc34-4707-814c-00f1fe43f831

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Digits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_PaddedDescent_F_MarkProf

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.Mark.Prof
theorem _root_.solution {g R A A' i : ℕ} (hA' : A' < g) (hi : i < R) :
    ((A * g + A') * R + i) % R = i ∧ ((A * g + A') * R + i) / R % g = A' ∧ ((A * g + A') * R + i) / R / g = A := by
  have hR : 0 < R := by omega
  have hg : 0 < g := by omega
  have h1 : ((A * g + A') * R + i) / R = A * g + A' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hi, Nat.zero_add]
  have h2 : ((A * g + A') * R + i) % R = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have h3 : (A * g + A') % g = A' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hA']
  have h4 : (A * g + A') / g = A := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hA', Nat.zero_add]
  rw [h1]
  exact ⟨h2, h3, h4⟩
end PaddedDescent.F.Mark.Prof
