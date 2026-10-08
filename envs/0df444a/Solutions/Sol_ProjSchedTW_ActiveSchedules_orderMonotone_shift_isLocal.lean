-- Prove2me | solution 1 for ProjSchedTW.ActiveSchedules.orderMonotone_shift_isLocal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:21:30.766103+00:00
-- url     : https://prove2.me/submissions/a7ea1322-0921-43e2-8c55-c635c7ad5144

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project
import Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts

namespace OMLocal9d4a

open ProjSchedTW.ActiveSchedules

lemma mem_activeSet' {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) (t : ℝ)
    (i : Fin (n + 2)) : i ∈ activeSet P S t ↔ S i ≤ t ∧ t < S i + (P.p i : ℝ) := by
  unfold activeSet
  simp

lemma feasible_of_order_sub {n : ℕ} {K : Type} (P : Project n K)
    (S x : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) (hx : x ∈ timeFeasibleSet P)
    (hO : scheduleOrder P S ⊆ scheduleOrder P x) : x ∈ feasibleSet P := by
  classical
  refine ⟨hx, hx.1, hx.2.1, ?_⟩
  intro k t _ht
  by_cases hA : (activeSet P x t).Nonempty
  · obtain ⟨m, hmA, hmax⟩ := (activeSet P x t).exists_max_image S hA
    have hsub : activeSet P x t ⊆ activeSet P S (S m) := by
      intro i hi
      rw [mem_activeSet'] at hi ⊢
      refine ⟨hmax i ((mem_activeSet' P x t i).2 hi), ?_⟩
      by_cases him : i = m
      · subst him
        have : (0 : ℝ) < (P.p i : ℝ) := by linarith [hi.1, hi.2]
        linarith
      · by_contra hcon
        replace hcon := not_lt.mp hcon
        have hmem : (i, m) ∈ scheduleOrder P S := ⟨him, hcon⟩
        have hx2 := (hO hmem).2
        rw [mem_activeSet'] at hmA
        simp only at hx2
        linarith [hmA.1, hi.2]
    calc usage P x k t = ∑ i ∈ activeSet P x t, P.r i k := rfl
      _ ≤ ∑ i ∈ activeSet P S (S m), P.r i k := Finset.sum_le_sum_of_subset hsub
      _ ≤ P.R k := hS.2.2.2 k (S m) (hS.2.2.1 m)
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    have : usage P x k t = 0 := by
      unfold usage; rw [hA]; simp
    rw [this]; exact Nat.zero_le _

lemma seg_time {n : ℕ} {K : Type} (P : Project n K) (S S' : Fin (n + 2) → ℝ)
    (hS : S ∈ timeFeasibleSet P) (hS' : S' ∈ timeFeasibleSet P) (τ : ℝ) (h0 : 0 ≤ τ)
    (h1 : τ ≤ 1) : (fun i => (1 - τ) * S i + τ * S' i) ∈ timeFeasibleSet P := by
  refine ⟨?_, ?_, ?_⟩
  · simp [hS.1, hS'.1]
  · intro i
    have := hS.2.1 i; have := hS'.2.1 i
    have : 0 ≤ 1 - τ := by linarith
    positivity
  · intro e he
    have a := hS.2.2 e he
    have b := hS'.2.2 e he
    have c : 0 ≤ 1 - τ := by linarith
    have := mul_le_mul_of_nonneg_left a c
    have := mul_le_mul_of_nonneg_left b h0
    simp only
    nlinarith

lemma seg_order {n : ℕ} {K : Type} (P : Project n K) (S S' T : Fin (n + 2) → ℝ)
    (hT : scheduleOrder P T ⊆ scheduleOrder P S ∧ scheduleOrder P T ⊆ scheduleOrder P S')
    (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    scheduleOrder P T ⊆ scheduleOrder P (fun i => (1 - τ) * S i + τ * S' i) := by
  intro e he
  have a := (hT.1 he).2
  have b := (hT.2 he).2
  refine ⟨he.1, ?_⟩
  have c : 0 ≤ 1 - τ := by linarith
  have := mul_le_mul_of_nonneg_left a c
  have := mul_le_mul_of_nonneg_left b h0
  simp only
  nlinarith

end OMLocal9d4a

open OMLocal9d4a in
open ProjSchedTW.ActiveSchedules in
theorem solution {n : ℕ} {K : Type} (P : ProjSchedTW.ActiveSchedules.Project n K)
    (S S' : Fin (n + 2) → ℝ) (h : ProjSchedTW.ActiveSchedules.IsOrderMonotoneShift P S S') :
    ProjSchedTW.ActiveSchedules.IsLocalShift P S S' := by
  obtain ⟨hg, hmono⟩ := h
  refine ⟨hg, fun τ i => (1 - (τ : ℝ)) * S i + (τ : ℝ) * S' i, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · funext i; simp
  · funext i; simp
  · intro τ
    have h0 : (0 : ℝ) ≤ τ := τ.2.1
    have h1 : (τ : ℝ) ≤ 1 := τ.2.2
    have ht := seg_time P S S' hg.1.1 hg.2.1.1 τ h0 h1
    rcases hmono with hm | hm
    · exact feasible_of_order_sub P S _ hg.1 ht
        (seg_order P S S' S ⟨subset_rfl, hm⟩ τ h0 h1)
    · exact feasible_of_order_sub P S' _ hg.2.1 ht
        (seg_order P S S' S' ⟨hm, subset_rfl⟩ τ h0 h1)
