-- Prove2me | solution 1 for SRPTManyServer.Collapse.capacity_constraint_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:58:22.494514+00:00
-- url     : https://prove2.me/submissions/4daa9d43-7146-4328-a606-a9000e1f7069

import Mathlib
import Definitions.Def_SRPTManyServer_Collapse_Model

open MeasureTheory Filter Topology SRPTManyServer.Collapse

lemma srpt_finite_arrived (x : Stream) (hx : x.Admissible) (u : ℝ) :
    {n : ℕ | x.A n ≤ u}.Finite := by
  obtain ⟨M, hM⟩ := (tendsto_atTop.mp hx.2.2.1 (u + 1)).exists_forall_of_atTop
  refine (Set.finite_lt_nat M).subset (fun n hn => ?_)
  simp only [Set.mem_setOf_eq] at hn ⊢
  by_contra h
  push_neg at h
  have := hM n h
  linarith

lemma srpt_delta_nonneg (x : Stream) (s : ℕ) (δ : ℕ → ℝ → ℝ) (hδ : IsSRPTSchedule s x δ)
    (n : ℕ) (u : ℝ) : 0 ≤ δ n u := by
  rcases hδ.1 n u with h | h <;> rw [h] <;> norm_num

lemma srpt_delta_le_one (x : Stream) (s : ℕ) (δ : ℕ → ℝ → ℝ) (hδ : IsSRPTSchedule s x δ)
    (n : ℕ) (u : ℝ) : δ n u ≤ 1 := by
  rcases hδ.1 n u with h | h <;> rw [h] <;> norm_num

lemma srpt_delta_ii (x : Stream) (s : ℕ) (δ : ℕ → ℝ → ℝ) (hδ : IsSRPTSchedule s x δ)
    (n : ℕ) (a b : ℝ) : IntervalIntegrable (δ n) volume a b := by
  refine intervalIntegrable_const (c := (1:ℝ)) |>.mono_fun (hδ.2.1 n).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun u => ?_)
  simp only [Real.norm_eq_abs, norm_one]
  rw [abs_of_nonneg (srpt_delta_nonneg x s δ hδ n u)]
  exact srpt_delta_le_one x s δ hδ n u

theorem solution (s : ℕ) (x : Stream) (hx : x.Admissible) (δ : ℕ → ℝ → ℝ)
    (hδ : IsSRPTSchedule s x δ) (t : ℝ) (ht : 0 ≤ t) :
    completedWork x δ t ≤ (s : ℝ) * t := by
  set F := {n | CompletedBy x δ n t} with hFdef
  have hF : F.Finite := (srpt_finite_arrived x hx t).subset (fun n hn => hn.1)
  unfold completedWork
  rw [← hFdef, finsum_mem_eq_finite_toFinset_sum _ hF]
  set G := hF.toFinset
  -- each completed customer's work is at most the service it got on [0, t]
  have hstep : ∀ n ∈ G, x.S n ≤ ∫ u in (0:ℝ)..t, δ n u := by
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    obtain ⟨hAn, hSn⟩ := hn
    have hA0 : 0 ≤ x.A n := by
      have h0 := hx.2.1
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h]; exact h0
      · exact h0.trans (hx.1.monotone (Nat.zero_le n))
    calc x.S n ≤ served x δ n t := hSn
      _ = ∫ u in (x.A n)..t, δ n u := rfl
      _ ≤ (∫ u in (0:ℝ)..(x.A n), δ n u) + ∫ u in (x.A n)..t, δ n u := by
          have : 0 ≤ ∫ u in (0:ℝ)..(x.A n), δ n u :=
            intervalIntegral.integral_nonneg hA0 (fun u _ => srpt_delta_nonneg x s δ hδ n u)
          linarith
      _ = ∫ u in (0:ℝ)..t, δ n u :=
          intervalIntegral.integral_add_adjacent_intervals (srpt_delta_ii x s δ hδ n _ _)
            (srpt_delta_ii x s δ hδ n _ _)
  have hpt : ∀ u : ℝ, ∑ n ∈ G, δ n u ≤ (s : ℝ) := by
    intro u
    have h1 : ∑ n ∈ G, δ n u = ∑ n ∈ G, (if δ n u = 1 then (1:ℝ) else 0) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rcases hδ.1 n u with h | h <;> simp [h]
    rw [h1, Finset.sum_boole]
    have hfin : {n | δ n u = 1}.Finite :=
      (srpt_finite_arrived x hx u).subset (fun n hn => (hδ.2.2.1 n u hn).1)
    have h2 : (G.filter (fun n => δ n u = 1)).card ≤ {n | δ n u = 1}.ncard := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard (fun n hn => ?_) hfin
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hn
      exact hn.2
    have h3 : {n | δ n u = 1}.ncard ≤ s := by
      rw [hδ.2.2.2.1 u]; exact min_le_left _ _
    exact_mod_cast h2.trans h3
  calc ∑ n ∈ G, x.S n ≤ ∑ n ∈ G, ∫ u in (0:ℝ)..t, δ n u := Finset.sum_le_sum hstep
    _ = ∫ u in (0:ℝ)..t, ∑ n ∈ G, δ n u :=
        (intervalIntegral.integral_finset_sum (fun n _ => srpt_delta_ii x s δ hδ n _ _)).symm
    _ ≤ ∫ u in (0:ℝ)..t, (s : ℝ) := by
        refine intervalIntegral.integral_mono_on ht ?_ intervalIntegrable_const
          (fun u _ => hpt u)
        refine intervalIntegrable_const (c := (s:ℝ)) |>.mono_fun
          (Finset.measurable_sum G (fun n _ => hδ.2.1 n)).aestronglyMeasurable ?_
        refine Filter.Eventually.of_forall (fun u => ?_)
        have h0 : 0 ≤ ∑ n ∈ G, δ n u :=
          Finset.sum_nonneg (fun n _ => srpt_delta_nonneg x s δ hδ n u)
        show ‖∑ n ∈ G, δ n u‖ ≤ |(s:ℝ)|
        rw [Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (by positivity)]
        exact hpt u
    _ = (s : ℝ) * t := by simp; ring
