-- Prove2me | solution 1 for RobustInventory.SingleStation.remark1_A_mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:41:28.675404+00:00
-- url     : https://prove2.me/submissions/2321dcb1-63ab-45cf-b17d-01400f34c3be

import Mathlib
import Definitions.Def_RobustInventory_SingleStation_Deviation

set_option autoImplicit false

open Finset in
theorem dca782cc_Γ_nonneg (M : RobustInventory.SingleStation.Model) (k : ℕ) : 0 ≤ M.Γ k := by
  induction k with
  | zero => exact M.hΓ0
  | succ n ih => exact le_trans ih (M.hΓmono n)

open Finset in
theorem dca782cc_bdd (M : RobustInventory.SingleStation.Model) (k : ℕ) :
    BddAbove {v : ℝ | ∃ z : ℕ → ℝ, M.LP13Feasible k z ∧
      v = ∑ i ∈ range (k + 1), M.what i * z i} := by
  refine ⟨∑ i ∈ range (k + 1), M.what i, ?_⟩
  rintro v ⟨z, ⟨hz, _⟩, rfl⟩
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 := (hz i hik).2
  have h0 := M.hwhat i
  nlinarith

open Finset in
theorem dca782cc_mem0 (M : RobustInventory.SingleStation.Model) (k : ℕ) :
    (0 : ℝ) ∈ {v : ℝ | ∃ z : ℕ → ℝ, M.LP13Feasible k z ∧
      v = ∑ i ∈ range (k + 1), M.what i * z i} := by
  refine ⟨fun _ => 0, ⟨fun i _ => ⟨le_refl _, zero_le_one⟩, ?_⟩, ?_⟩
  · simp only [Finset.sum_const_zero]
    exact dca782cc_Γ_nonneg M k
  · simp

open Finset in
theorem dca782cc_A_step (M : RobustInventory.SingleStation.Model) (k : ℕ) :
    M.A k ≤ M.A (k + 1) := by
  unfold RobustInventory.SingleStation.Model.A
  apply csSup_le_csSup (dca782cc_bdd M (k + 1)) ⟨0, dca782cc_mem0 M k⟩
  rintro v ⟨z, ⟨hz, hs⟩, rfl⟩
  refine ⟨fun i => if i ≤ k then z i else 0, ⟨?_, ?_⟩, ?_⟩
  · intro i _
    by_cases h : i ≤ k
    · simp only [h, if_true]; exact hz i h
    · simp only [h, if_false]; exact ⟨le_refl _, zero_le_one⟩
  · rw [Finset.sum_range_succ]
    have e : ∑ x ∈ range (k + 1), (if x ≤ k then z x else 0) = ∑ x ∈ range (k + 1), z x := by
      apply Finset.sum_congr rfl
      intro x hx
      have : x ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      simp [this]
    rw [e]
    simp only [show ¬ (k + 1 ≤ k) from by omega, if_false, add_zero]
    exact le_trans hs (M.hΓmono k)
  · conv_rhs => rw [Finset.sum_range_succ]
    simp only [show ¬ (k + 1 ≤ k) from by omega, if_false, mul_zero, add_zero]
    symm
    apply Finset.sum_congr rfl
    intro x hx
    have : x ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
    simp [this]

theorem dca782cc_mono (M : RobustInventory.SingleStation.Model) (k : ℕ) : M.Aprev k ≤ M.A k := by
  cases k with
  | zero =>
    show (0 : ℝ) ≤ M.A 0
    exact le_csSup (dca782cc_bdd M 0) (dca782cc_mem0 M 0)
  | succ n => exact dca782cc_A_step M n

open RobustInventory.SingleStation in
theorem solution (M : Model) :
    (∀ k, M.Aprev k ≤ M.A k) ∧
    (M.h ≤ M.p → ∀ k, M.wbar k ≤ M.wmod k) ∧
    (M.p ≤ M.h → ∀ k, M.wmod k ≤ M.wbar k) := by
  have hpos : 0 < M.p + M.h := by linarith [M.hc, M.hpc, M.hh]
  refine ⟨dca782cc_mono M, ?_, ?_⟩
  · intro hhp k
    unfold Model.wmod
    have hd : 0 ≤ M.A k - M.Aprev k := sub_nonneg.mpr (dca782cc_mono M k)
    have hc : 0 ≤ (M.p - M.h) / (M.p + M.h) := div_nonneg (by linarith) hpos.le
    nlinarith [mul_nonneg hc hd]
  · intro hph k
    unfold Model.wmod
    have hd : 0 ≤ M.A k - M.Aprev k := sub_nonneg.mpr (dca782cc_mono M k)
    have hc : (M.p - M.h) / (M.p + M.h) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hd]
