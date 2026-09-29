-- Prove2me | solution 1 for Zeta23.Tail.sum_window_weights_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:02:48.598036+00:00
-- url     : https://prove2.me/submissions/16dcbf80-9b58-418c-8a7f-e646faa671fe

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Zeta23_Tail_Basic

-- from Zeta23.Tail.Count
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Count.lean — the zero-count sum in the proof of [prop:tail] (the paper §4.2).


Paper, verbatim: "It remains to bound ∑_{γ∉I'} m_ρ D⁻³ (zeros counted with multiplicity).
Zeros with γ > 2T+D₀: grouping them into γ ∈ (2T+D₀+j, 2T+D₀+j+1], j ≥ 0, this part is at
most ∑_{j≥0} A₀ log(2T+D₀+j+4)(D₀+j)⁻³ ≤ (3/2)A₀ log(4T) D₀⁻² for T large (split at j = T
and use D₀ ≥ 2). Zeros with 0 < γ < T−D₀ contribute likewise at most (3/2)A₀ log(4T)D₀⁻²,
and zeros with γ ≤ 0 have D ≥ T and contribute at most ∑_{j≥0} A₀ log(j+4)(T+j)⁻³
≪ T⁻² log T. Altogether ∑_{γ∉I'} m_ρ D⁻³ ≤ 4A₀ log(4T) D₀⁻² for T ≥ T₀."

We prove the bound for every FINITE sub-family of tail zeros (which yields both the
summability and the bound for the full series downstream), with the explicit absolute
threshold T₀ of Zeta23/Tail/Basic.lean. Only the final constant 4 is load-bearing (it is
the 4 in θ₀); we do not follow the paper's intermediate 3/2 + 3/2 + o(1) split. Our
grouping: unit windows indexed by the integer distance j from the nearer endpoint of
I = [T,2T] (lower side: T−j−1 < γ ≤ T−j, which also covers ALL γ ≤ 0; upper side:
2T+j < γ ≤ 2T+j+1), each window weighted by max(D₀, j)⁻³ and counted by the two-sided
local count ≤ A₀ log(2T+4+j); integrals are replaced by telescoping sums.
-/

noncomputable section

open Finset Real

namespace Zeta23
namespace Tail

/-! #### Telescoping sums replacing ∫ x⁻³ and ∫ x⁻² -/

lemma inv_pow_three_step {a : ℝ} (ha : 0 < a) :
    ((a + 1) ^ 3)⁻¹ ≤ ((a ^ 2)⁻¹ - ((a + 1) ^ 2)⁻¹) / 2 := by
  rw [← sub_nonneg]
  have key : ((a ^ 2)⁻¹ - ((a + 1) ^ 2)⁻¹) / 2 - ((a + 1) ^ 3)⁻¹
      = (3 * a + 1) / (2 * a ^ 2 * (a + 1) ^ 3) := by
    field_simp; ring
  rw [key]; positivity

lemma inv_pow_two_step {a : ℝ} (ha : 0 < a) :
    ((a + 1) ^ 2)⁻¹ ≤ a⁻¹ - (a + 1)⁻¹ := by
  rw [← sub_nonneg]
  have key : a⁻¹ - (a + 1)⁻¹ - ((a + 1) ^ 2)⁻¹ = 1 / (a * (a + 1) ^ 2) := by
    field_simp; ring
  rw [key]; positivity

lemma sum_inv_pow_three_le_telescope {D : ℝ} (hD : 0 < D) (n : ℕ) :
    ∑ i ∈ range (n + 1), ((D + i) ^ 3)⁻¹ ≤ (D ^ 3)⁻¹ + ((D ^ 2)⁻¹ - ((D + n) ^ 2)⁻¹) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hstep := inv_pow_three_step (a := D + n) (by positivity)
    have e : (D + ((n + 1 : ℕ) : ℝ)) = D + n + 1 := by push_cast; ring
    rw [e]
    calc _ ≤ (D ^ 3)⁻¹ + ((D ^ 2)⁻¹ - ((D + n) ^ 2)⁻¹) / 2
          + (((D + n) ^ 2)⁻¹ - ((D + n + 1) ^ 2)⁻¹) / 2 := add_le_add ih hstep
      _ = _ := by ring

lemma sum_inv_pow_two_le_telescope {D : ℝ} (hD : 0 < D) (n : ℕ) :
    ∑ i ∈ range (n + 1), ((D + i) ^ 2)⁻¹ ≤ (D ^ 2)⁻¹ + (D⁻¹ - (D + n)⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hstep := inv_pow_two_step (a := D + n) (by positivity)
    have e : (D + ((n + 1 : ℕ) : ℝ)) = D + n + 1 := by push_cast; ring
    rw [e]
    calc _ ≤ (D ^ 2)⁻¹ + (D⁻¹ - (D + n)⁻¹) + ((D + n)⁻¹ - (D + n + 1)⁻¹) :=
          add_le_add ih hstep
      _ = _ := by ring

/-- ∑_{i<n} (D + i)⁻³ ≤ D⁻³ + D⁻²/2 for D > 0 (any n). -/
lemma sum_inv_pow_three_le {D : ℝ} (hD : 0 < D) (n : ℕ) :
    ∑ i ∈ range n, ((D + i) ^ 3)⁻¹ ≤ (D ^ 3)⁻¹ + (D ^ 2)⁻¹ / 2 := by
  cases n with
  | zero => simp only [range_zero, sum_empty]; positivity
  | succ n =>
    refine (sum_inv_pow_three_le_telescope hD n).trans ?_
    have : 0 ≤ ((D + n) ^ 2)⁻¹ := by positivity
    linarith

/-- ∑_{i<n} (D + i)⁻² ≤ D⁻² + D⁻¹ for D > 0 (any n). -/
lemma sum_inv_pow_two_le {D : ℝ} (hD : 0 < D) (n : ℕ) :
    ∑ i ∈ range n, ((D + i) ^ 2)⁻¹ ≤ (D ^ 2)⁻¹ + D⁻¹ := by
  cases n with
  | zero => simp only [range_zero, sum_empty]; positivity
  | succ n =>
    refine (sum_inv_pow_two_le_telescope hD n).trans ?_
    have : 0 ≤ (D + n)⁻¹ := by positivity
    linarith

/-- log(B + j) ≤ log B + j/B. -/
lemma log_add_le_log_add_div {B j : ℝ} (hB : 0 < B) (hj : 0 ≤ j) :
    Real.log (B + j) ≤ Real.log B + j / B := by
  have e : B + j = B * (1 + j / B) := by field_simp
  rw [e, Real.log_mul hB.ne' (by positivity)]
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + j / B by positivity)
  linarith

/-! #### Summing the window weights -/


/-! #### One side of the tail, abstractly -/


/-! #### Numerics at T ≥ T₀ -/



/-! #### The zero-count sum -/


/-! #### The boundary count N(I' ∖ I) -/



end Tail
end Zeta23
end
open Finset Real
open Zeta23
open Tail

theorem solution (F : Finset ℕ) {B D₀ : ℝ} (hB : 1 ≤ B) (hD₀ : 2 ≤ D₀)
    (hF : ∀ j ∈ F, D₀ ≤ (j : ℝ) + 1) :
    ∑ j ∈ F, ((max D₀ j) ^ 3)⁻¹ * Real.log (B + j)
      ≤ (2 * (D₀ ^ 3)⁻¹ + (D₀ ^ 2)⁻¹ / 2) * Real.log B + (2 * (D₀ ^ 2)⁻¹ + D₀⁻¹) / B := by
  have hB0 : 0 < B := by linarith
  have hD0 : 0 < D₀ := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  set g : ℕ → ℝ := fun j => ((max D₀ j) ^ 3)⁻¹ * Real.log (B + j) with hg
  have hg_nn : ∀ j, 0 ≤ g j := fun j => by
    have : 1 ≤ B + j := by have := (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith
    exact mul_nonneg (by positivity) (Real.log_nonneg this)
  -- F ⊆ Ico J₀ N with J₀ := ⌈D₀⌉₊ − 1.
  set J₀ : ℕ := ⌈D₀⌉₊ - 1 with hJ₀
  have hceil : 1 ≤ ⌈D₀⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hJ₀succ : J₀ + 1 = ⌈D₀⌉₊ := Nat.sub_add_cancel hceil
  have hJ₀le : (J₀ : ℝ) ≤ D₀ := by
    have h1 : ((J₀ + 1 : ℕ) : ℝ) = ⌈D₀⌉₊ := by rw [hJ₀succ]
    have h2 : (⌈D₀⌉₊ : ℝ) < D₀ + 1 := Nat.ceil_lt_add_one hD0.le
    push_cast at h1; linarith
  have hJ₀ge : ∀ i : ℕ, D₀ + i ≤ ((J₀ + 1 + i : ℕ) : ℝ) := fun i => by
    rw [hJ₀succ]; push_cast; linarith [Nat.le_ceil D₀]
  set N : ℕ := F.sup id + 1
  have hsub : F ⊆ Finset.Ico J₀ N := by
    intro j hj
    rw [Finset.mem_Ico]
    refine ⟨?_, Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)⟩
    have : ⌈D₀⌉₊ ≤ j + 1 := Nat.ceil_le.mpr (by exact_mod_cast hF j hj)
    omega
  calc ∑ j ∈ F, g j
      ≤ ∑ j ∈ Finset.Ico J₀ N, g j :=
        sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hg_nn j
    _ = ∑ i ∈ range (N - J₀), g (J₀ + i) := Finset.sum_Ico_eq_sum_range _ _ _
    _ ≤ _ := ?_
  rcases Nat.eq_zero_or_eq_succ_pred (N - J₀) with h0 | hsucc
  · rw [h0, sum_range_zero]; positivity
  set n := (N - J₀).pred
  rw [hsucc, sum_range_succ']
  -- the first window j = J₀ ≤ D₀: weight D₀⁻³, log(B + J₀) ≤ log B + D₀/B.
  have hfirst : g (J₀ + 0) ≤ (D₀ ^ 3)⁻¹ * Real.log B + (D₀ ^ 2)⁻¹ / B := by
    simp only [hg, add_zero]
    have hmax : max D₀ (J₀ : ℝ) = D₀ := max_eq_left hJ₀le
    rw [hmax]
    have hl : Real.log (B + J₀) ≤ Real.log B + D₀ / B :=
      (log_add_le_log_add_div hB0 (Nat.cast_nonneg _)).trans
        (by gcongr)
    calc (D₀ ^ 3)⁻¹ * Real.log (B + J₀) ≤ (D₀ ^ 3)⁻¹ * (Real.log B + D₀ / B) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by field_simp
  -- the windows j = J₀ + 1 + i ≥ D₀ + i: weight j⁻³, log(B+j) ≤ log B + j/B.
  have hrest : ∀ i ∈ range n, g (J₀ + (i + 1))
      ≤ ((D₀ + i) ^ 3)⁻¹ * Real.log B + ((D₀ + i) ^ 2)⁻¹ / B := by
    intro i _
    simp only [hg]
    have hji : D₀ + i ≤ ((J₀ + (i + 1) : ℕ) : ℝ) := by
      have := hJ₀ge i; rw [show J₀ + 1 + i = J₀ + (i + 1) by ring] at this; exact this
    set j : ℝ := ((J₀ + (i + 1) : ℕ) : ℝ) with hj
    have hDi : 0 < D₀ + i := by positivity
    have hjpos : 0 < j := lt_of_lt_of_le hDi hji
    have hmax : max D₀ j = j := max_eq_right (by
      have := (Nat.cast_nonneg i : (0:ℝ) ≤ i); linarith)
    rw [hmax]
    have hl : Real.log (B + j) ≤ Real.log B + j / B :=
      log_add_le_log_add_div hB0 hjpos.le
    calc (j ^ 3)⁻¹ * Real.log (B + j) ≤ (j ^ 3)⁻¹ * (Real.log B + j / B) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = (j ^ 3)⁻¹ * Real.log B + (j ^ 2)⁻¹ / B := by field_simp
      _ ≤ ((D₀ + i) ^ 3)⁻¹ * Real.log B + ((D₀ + i) ^ 2)⁻¹ / B := by
          gcongr
  calc ∑ i ∈ range n, g (J₀ + (i + 1)) + g (J₀ + 0)
      ≤ ∑ i ∈ range n, (((D₀ + i) ^ 3)⁻¹ * Real.log B + ((D₀ + i) ^ 2)⁻¹ / B)
        + ((D₀ ^ 3)⁻¹ * Real.log B + (D₀ ^ 2)⁻¹ / B) := add_le_add (sum_le_sum hrest) hfirst
    _ = (∑ i ∈ range n, ((D₀ + i) ^ 3)⁻¹) * Real.log B
        + (∑ i ∈ range n, ((D₀ + i) ^ 2)⁻¹) / B
        + ((D₀ ^ 3)⁻¹ * Real.log B + (D₀ ^ 2)⁻¹ / B) := by
          rw [sum_add_distrib, sum_mul, sum_div]
    _ ≤ ((D₀ ^ 3)⁻¹ + (D₀ ^ 2)⁻¹ / 2) * Real.log B + ((D₀ ^ 2)⁻¹ + D₀⁻¹) / B
        + ((D₀ ^ 3)⁻¹ * Real.log B + (D₀ ^ 2)⁻¹ / B) := by
          gcongr
          · exact sum_inv_pow_three_le hD0 n
          · exact sum_inv_pow_two_le hD0 n
    _ = _ := by ring
