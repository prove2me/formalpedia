-- Prove2me | solution 1 for UniformInK.Budget.leafCU_add_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:32:42.240528+00:00
-- url     : https://prove2.me/submissions/f508a54d-4632-4701-8dfa-99fb1cf6b5d4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_UniformInK_Top_Budget
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open UniformInK UniformInK.Budget
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL UniformInK.Leaves
namespace UniformInK.Budget
theorem _root_.solution {τ : ℕ} (hτ : 8 ≤ τ) {k : ℕ} (hk : 1 ≤ k) : leafCU τ k + 2 ≤ τ ^ (2 * k) := by
  unfold leafCU
  induction k, hk using Nat.le_induction with
  | base =>
    have h : 8 * 8 ≤ τ * τ := Nat.mul_le_mul hτ hτ
    rw [Finset.range_one, Finset.sum_singleton, Nat.mul_one, sq, show thetaU τ 0 = 1 from rfl]
    omega
  | succ k hk ih =>
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_range_succ, show thetaU τ (i + 1) = 4 * τ ^ (2 * i + 1) from rfl]
    have e1 : τ ^ (2 * (i + 1)) = τ * τ ^ (2 * i + 1) := by rw [show 2 * (i + 1) = (2 * i + 1) + 1 by ring, pow_succ]; ring
    have e2 : τ ^ (2 * (i + 1 + 1)) = τ * τ * τ ^ (2 * (i + 1)) := by rw [show 2 * (i + 1 + 1) = 2 * (i + 1) + 2 by ring, pow_add]; ring
    have h1 : 8 * τ ^ (2 * i + 1) ≤ τ ^ (2 * (i + 1)) := by rw [e1]; exact Nat.mul_le_mul_right _ hτ
    have h2 : 2 * τ ^ (2 * (i + 1)) ≤ τ ^ (2 * (i + 1 + 1)) := by rw [e2]; exact Nat.mul_le_mul_right _ (by nlinarith)
    omega
end UniformInK.Budget
