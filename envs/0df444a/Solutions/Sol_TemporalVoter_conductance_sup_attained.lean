-- Prove2me | solution 1 for TemporalVoter.conductance_sup_attained
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:41:06.389195+00:00
-- url     : https://prove2.me/submissions/82a10d50-08ce-4706-a95d-0dbbde918fc6

import Mathlib
import Definitions.Def_TemporalVoter_temporalConductance

namespace Aux_TV_sup
open TemporalVoter

theorem sup_attained (f : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf0 : ∀ n, 0 ≤ f n)
    (hfB : ∀ n, f n ≤ B / ((n : ℝ) + 1)) : ∃ n, ⨆ k, f k = f n := by
  have hfB' : ∀ n, f n ≤ B := fun n => (hfB n).trans
    (div_le_self hB (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith))
  have bdd : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hfB' n⟩
  by_cases hs : ⨆ k, f k ≤ 0
  · exact ⟨0, le_antisymm (hs.trans (hf0 0)) (le_ciSup bdd 0)⟩
  push_neg at hs
  set s := ⨆ k, f k
  obtain ⟨N, hN⟩ := exists_nat_gt (B / s)
  have hNs : B / ((N : ℝ) + 1) < s := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hs] at hN
    nlinarith
  obtain ⟨n, _, hmax⟩ := Finset.exists_max_image (Finset.range (N + 1)) f ⟨0, by simp⟩
  refine ⟨n, le_antisymm ?_ (le_ciSup bdd n)⟩
  have : s ≤ max (f n) (B / ((N : ℝ) + 1)) := by
    apply ciSup_le
    intro m
    by_cases hm : m ≤ N
    · exact le_max_of_le_left (hmax m (by simp; omega))
    · apply le_max_of_le_right
      refine (hfB m).trans ?_
      apply div_le_div_of_nonneg_left hB (by positivity)
      have : (N : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : N + 1 ≤ m)
      linarith
  rcases le_max_iff.mp this with h | h
  · exact h
  · linarith

theorem condAt_bounds {V : Type} [Fintype V] (T : TemporalGraph V) (t : ℕ) (S : Finset V) :
    0 ≤ condAt T t S ∧ condAt T t S ≤ (Fintype.card (V × V) : ℝ) := by
  have hcut0 : 0 ≤ T.cut t S := Nat.cast_nonneg _
  have hcut : T.cut t S ≤ (Fintype.card (V × V) : ℝ) := by
    unfold TemporalGraph.cut SpectralSparsify.Decomp.cutEdges
    exact_mod_cast Finset.card_le_univ _
  have hvol0 : 0 ≤ T.vol S := Finset.sum_nonneg (fun v _ => Nat.cast_nonneg _)
  unfold condAt
  refine ⟨div_nonneg hcut0 hvol0, ?_⟩
  by_cases hv : T.vol S = 0
  · rw [hv, div_zero]; positivity
  · have hS : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; rintro rfl; apply hv; simp [TemporalGraph.vol]
    obtain ⟨v, hv'⟩ := hS
    have h1 : (1 : ℝ) ≤ T.vol S := by
      have := Finset.single_le_sum (f := fun v => (T.d v : ℝ)) (fun v _ => Nat.cast_nonneg _) hv'
      have h2 : (1 : ℝ) ≤ T.d v := by exact_mod_cast T.one_le_d v
      unfold TemporalGraph.vol; linarith
    exact (div_le_self hcut0 h1).trans hcut

theorem window_bounds {V : Type} [Fintype V] (T : TemporalGraph V) (Δ : ℕ) :
    0 ≤ windowCond T Δ ∧ windowCond T Δ ≤ (Fintype.card (V × V) : ℝ) := by
  set B := (Fintype.card (V × V) : ℝ)
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hset : ∀ a b S, 0 ≤ intervalCondSet T a b S ∧ intervalCondSet T a b S ≤ B := by
    intro a b S
    unfold intervalCondSet
    exact ⟨Real.iSup_nonneg (fun t => (condAt_bounds T t S).1),
      Real.iSup_le (fun t => (condAt_bounds T t S).2) hB⟩
  have hint : ∀ a b, 0 ≤ intervalCond T a b ∧ intervalCond T a b ≤ B := by
    intro a b
    unfold intervalCond
    refine ⟨Real.iInf_nonneg (fun S => (hset a b S.1).1), ?_⟩
    rcases isEmpty_or_nonempty {S : Finset V // 0 < T.vol S ∧ T.vol S ≤ T.m} with h | hne
    · rw [Real.iInf_of_isEmpty]; exact hB
    · obtain ⟨S⟩ := hne
      exact (ciInf_le ⟨0, by rintro _ ⟨S, rfl⟩; exact (hset a b S.1).1⟩ S).trans (hset a b S.1).2
  unfold windowCond
  refine ⟨Real.iInf_nonneg (fun t => (hint _ _).1), ?_⟩
  exact (ciInf_le ⟨0, by rintro _ ⟨t, rfl⟩; exact (hint _ _).1⟩ 0).trans (hint _ _).2

end Aux_TV_sup

open TemporalVoter Aux_TV_sup in
theorem solution {V : Type} [Fintype V] (T : TemporalGraph V) :
    ∃ Δ : ℕ, 1 ≤ Δ ∧ temporalConductance T = windowCond T Δ / (Δ : ℝ) := by
  set B := (Fintype.card (V × V) : ℝ)
  obtain ⟨n, hn⟩ := sup_attained (fun Δ => windowCond T (Δ + 1) / ((Δ + 1 : ℕ) : ℝ)) B
    (Nat.cast_nonneg _)
    (fun Δ => div_nonneg (window_bounds T _).1 (Nat.cast_nonneg _))
    (fun Δ => by
      push_cast
      exact div_le_div_of_nonneg_right (window_bounds T _).2 (by positivity))
  exact ⟨n + 1, by omega, hn⟩
