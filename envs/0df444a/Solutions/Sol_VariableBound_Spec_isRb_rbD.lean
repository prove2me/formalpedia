-- Prove2me | solution 1 for VariableBound.Spec.isRb_rbD
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:25:45.236252+00:00
-- url     : https://prove2.me/submissions/8500e63f-ed6a-40fe-94a0-dcef6557c138

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Spec
set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Spec

/-- If `p` holds below `N` exactly at the numbers below `k`, it holds at `min N k`
numbers below `N`. -/
private theorem length_filter_range (p : ℕ → Bool) (N k : ℕ)
    (h : ∀ j < N, (p j = true ↔ j < k)) : ((List.range N).filter p).length = min N k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append,
      ih fun j hj => h j (Nat.lt_succ_of_lt hj)]
    have hN := h N (Nat.lt_succ_self N)
    by_cases hk : N < k
    · rw [List.filter_singleton, hN.2 hk]
      simp only [cond_true, List.length_singleton]
      omega
    · have hf : p N = false := by
        rcases hb : p N with _ | _
        · rfl
        · exact absurd (hN.1 hb) hk
      rw [List.filter_singleton, hf]
      simp only [cond_false, List.length_nil]
      omega

/-- Let `P` be closed upwards and hold at some number `j ≤ N`, and let `p` decide `¬ P`.
Then the number of `j < N` with `p j` is the least number at which `P` holds. -/
private theorem count_spec (P : ℕ → Prop) (p : ℕ → Bool) (N : ℕ)
    (hp : ∀ j, p j = true ↔ ¬ P j) (up : ∀ j, P j → P (j + 1))
    (hN : ∃ j ≤ N, P j) :
    P ((List.range N).filter p).length ∧
      ∀ j < ((List.range N).filter p).length, ¬ P j := by
  classical
  obtain ⟨j₀, hj₀, hP⟩ := hN
  have hex : ∃ j, P j := ⟨j₀, hP⟩
  have hk : Nat.find hex ≤ N := (Nat.find_min' hex hP).trans hj₀
  have hmono : ∀ j, Nat.find hex ≤ j → P j := fun j hj =>
    Nat.le_induction (Nat.find_spec hex) (fun i _ hi => up i hi) j hj
  have hlen : ((List.range N).filter p).length = Nat.find hex := by
    rw [length_filter_range p N (Nat.find hex) fun j _ =>
      (hp j).trans ⟨fun h => not_le.1 fun hle => h (hmono j hle),
        fun h => Nat.find_min hex h⟩]
    exact min_eq_right hk
  rw [hlen]
  exact ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩

theorem solution (β : ℕ) : IsRb β (rbD β) := by
  refine count_spec (fun j => 3 ^ j * 2 ^ β < 4 ^ j) _ (3 * β + 2)
    (fun j => by simp only [decide_eq_true_eq]) (fun j hj => ?_)
    ⟨3 * β + 1, by omega, ?_⟩
  · rw [pow_succ, pow_succ]
    have : 0 < 4 ^ j := by positivity
    nlinarith
  · have h : (54 : ℕ) ^ β ≤ 64 ^ β := Nat.pow_le_pow_left (by norm_num) β
    have e1 : 3 ^ (3 * β + 1) * 2 ^ β = 3 * 54 ^ β := by
      rw [pow_succ, pow_mul, show (54 : ℕ) = 3 ^ 3 * 2 by norm_num, mul_pow]
      ring
    have e2 : 4 ^ (3 * β + 1) = 4 * 64 ^ β := by
      rw [pow_succ, pow_mul]
      norm_num [mul_comm]
    have : 0 < 64 ^ β := by positivity
    rw [e1, e2]
    omega
