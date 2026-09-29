-- Prove2me | solution 1 for bernoulli_event_failure_lower_bound_from_cardinality_failures
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T04:17:56.464402+00:00
-- url     : https://prove2.me/submissions/91c077e8-3aa5-404f-985c-2abbcd523c79

import Definitions.Def_matrix_completion_fixed_cardinality
import Theorems.Thm_bernoulli_event_success_probability_decomposes_by_cardinality
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators
open Finset

theorem solution {n₁ n₂ : ℕ} (p : ℝ) (m : ℕ)
    (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 → m ≤ n₁ * n₂ →
    (∀ k : ℕ, k ≤ m →
      1 - fixedCardinalityEventProb m Event ≤
        1 - fixedCardinalityEventProb k Event) →
    (1 / 2 : ℝ) ≤ binomialLowerTailProb (n₁ * n₂) m p →
    (1 / 2) * (1 - fixedCardinalityEventProb m Event) ≤
      1 - bernoulliEventProb p Event := by
  intro hp0 hp1 hmN hmono hL
  set N := n₁ * n₂ with hN
  set w : ℕ → ℝ := fun k => binomialCardinalityProb N k p with hw
  set fc : ℕ → ℝ := fun k => fixedCardinalityEventProb k Event with hfc
  -- weight nonneg
  have hwnn : ∀ k, 0 ≤ w k := by
    intro k
    simp only [hw, binomialCardinalityProb]
    have h1mp : (0:ℝ) ≤ 1 - p := by linarith
    positivity
  -- fc ≤ 1, hence 1 - fc ≥ 0
  have hfc_le_one : ∀ k, fc k ≤ 1 := by
    intro k
    simp only [hfc, fixedCardinalityEventProb]
    set S := Finset.powersetCard k (Finset.univ : Finset (Fin n₁ × Fin n₂)) with hS
    rcases Nat.eq_zero_or_pos S.card with hc | hc
    · simp [hc]
    · rw [div_le_one (by exact_mod_cast hc)]
      have : (S.filter Event).card ≤ S.card := Finset.card_filter_le _ _
      exact_mod_cast this
  have hg_nn : ∀ k, 0 ≤ 1 - fc k := by intro k; linarith [hfc_le_one k]
  -- full sum of weights = 1
  have hfull : ∑ k ∈ Finset.range (N + 1), w k = 1 := by
    have hb := add_pow p (1 - p) N
    rw [add_sub_cancel, one_pow] at hb
    rw [hb]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [hw, binomialCardinalityProb]
    ring
  -- decompose bernoulli
  have hdecomp : bernoulliEventProb p Event
      = ∑ k ∈ Finset.range (N + 1), w k * fc k :=
    bernoulli_event_success_probability_decomposes_by_cardinality p Event hp0 hp1
  -- 1 - bernoulli = ∑ w k (1 - fc k)
  have hfail : 1 - bernoulliEventProb p Event
      = ∑ k ∈ Finset.range (N + 1), w k * (1 - fc k) := by
    have hrw : ∑ k ∈ Finset.range (N + 1), w k * (1 - fc k)
        = (∑ k ∈ Finset.range (N + 1), w k) - ∑ k ∈ Finset.range (N + 1), w k * fc k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk; ring
    rw [hrw, hfull, hdecomp]
  rw [hfail]
  -- abbreviate gm
  set gm : ℝ := 1 - fc m with hgm
  have hgm_nn : 0 ≤ gm := hg_nn m
  -- step 1: restrict to range (m+1) (tail nonneg)
  have hsub : Finset.range (m + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    exact lt_of_lt_of_le hx (Nat.add_le_add_right hmN 1)
  have hstep1 :
      ∑ k ∈ Finset.range (m + 1), w k * (1 - fc k)
        ≤ ∑ k ∈ Finset.range (N + 1), w k * (1 - fc k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k _ _
    exact mul_nonneg (hwnn k) (hg_nn k)
  -- step 2: on range (m+1), 1 - fc k ≥ gm
  have hstep2 :
      ∑ k ∈ Finset.range (m + 1), w k * gm
        ≤ ∑ k ∈ Finset.range (m + 1), w k * (1 - fc k) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp hk
    have hmono_k : gm ≤ 1 - fc k := hmono k hkm
    exact mul_le_mul_of_nonneg_left hmono_k (hwnn k)
  -- step 3: ∑ w k * gm = (∑ w k) * gm = binomialLowerTailProb N m p * gm
  have hsum_wgm : ∑ k ∈ Finset.range (m + 1), w k * gm
      = binomialLowerTailProb N m p * gm := by
    rw [← Finset.sum_mul]
    congr 1
  have hstep3 : (1 / 2) * gm ≤ binomialLowerTailProb N m p * gm := by
    apply mul_le_mul_of_nonneg_right hL hgm_nn
  -- chain
  calc (1 / 2) * gm
      ≤ binomialLowerTailProb N m p * gm := hstep3
    _ = ∑ k ∈ Finset.range (m + 1), w k * gm := hsum_wgm.symm
    _ ≤ ∑ k ∈ Finset.range (m + 1), w k * (1 - fc k) := hstep2
    _ ≤ ∑ k ∈ Finset.range (N + 1), w k * (1 - fc k) := hstep1
