-- Prove2me | solution 1 for ScheduledQueue.Stability.lower_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:51:02.949003+00:00
-- url     : https://prove2.me/submissions/af5d2cc5-1138-4352-afe2-10539db768a1

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

open ScheduledQueue.Stability in
theorem solution {Ω : Type*} (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ)
    (U : Ω → ℝ) :
    ∀ ω, U ω ∈ Icc (0 : ℝ) 1 → ∀ n : ℕ,
      (n : ℕ∞) + tildeY h ξ n ω ≤ revCount h ξ U (n * h) ω + Y h ξ n ω + gamma2 h ξ ω := by
  intro ω hU n
  set A : Set ℤ := (Finset.Icc (1 : ℤ) n : Set ℤ)
  set Tset : Set ℤ := {j : ℤ | 1 ≤ j ∧ (j + 2) * h ≤ max (ξ ((n : ℤ) + j) ω) 0}
  set Yset : Set ℤ := {j : ℤ | 1 ≤ j ∧ (j - 2) * h < -ξ ((n : ℤ) + 1 - j) ω}
  set Rset : Set ℤ := {j : ℤ | revArrival h ξ U j ω ∈ Ioc 0 (n * h)}
  set Gset : Set ℤ := {j : ℤ | 1 ≤ j ∧ (j - 1) * h ≤ ξ j ω}
  have hA : A.encard = n := by
    simp only [A]; rw [Set.encard_coe_eq_coe_finsetCard, Int.card_Icc]; simp
  have hT : ((fun i : ℤ => (n : ℤ) + i) '' Tset).encard = tildeY h ξ n ω :=
    (add_right_injective _).encard_image _
  have hY : ((fun i : ℤ => (n : ℤ) + 1 - i) '' Yset).encard = Y h ξ n ω :=
    Function.Injective.encard_image (fun a b hab => by simpa using hab) _
  have hdisj : Disjoint A ((fun i : ℤ => (n : ℤ) + i) '' Tset) := by
    rw [Set.disjoint_left]
    rintro j hjA ⟨i, hi, rfl⟩
    simp only [A, Finset.coe_Icc, mem_Icc] at hjA
    have := hi.1
    omega
  have hsub : A ∪ ((fun i : ℤ => (n : ℤ) + i) '' Tset) ⊆
      Rset ∪ ((fun i : ℤ => (n : ℤ) + 1 - i) '' Yset) ∪ Gset := by
    rintro j (hjA | ⟨i, hi, rfl⟩)
    · simp only [A, Finset.coe_Icc, mem_Icc] at hjA
      by_cases h1 : revArrival h ξ U j ω ≤ 0
      · right
        refine ⟨hjA.1, ?_⟩
        simp only [revArrival] at h1
        nlinarith [hU.1]
      by_cases h2 : revArrival h ξ U j ω ≤ n * h
      · left; left; exact ⟨lt_of_not_ge h1, h2⟩
      · left; right
        refine ⟨(n : ℤ) + 1 - j, ⟨by omega, ?_⟩, by ring⟩
        simp only [revArrival, not_le] at h2
        have e : (n : ℤ) + 1 - ((n : ℤ) + 1 - j) = j := by ring
        rw [e]
        push_cast
        nlinarith [hU.2]
    · obtain ⟨hi1, hi2⟩ := hi
      have hipos : (0 : ℝ) < (i + 2) * h := by
        have : (1 : ℝ) ≤ i := by exact_mod_cast hi1
        nlinarith
      have hξ : ((i : ℝ) + 2) * h ≤ ξ ((n : ℤ) + i) ω := by
        rcases le_total (ξ ((n : ℤ) + i) ω) 0 with hle | hle
        · rw [max_eq_right hle] at hi2; linarith
        · rwa [max_eq_left hle] at hi2
      by_cases h1 : revArrival h ξ U ((n : ℤ) + i) ω ≤ 0
      · right
        refine ⟨show (1:ℤ) ≤ (n:ℤ) + i by omega, ?_⟩
        simp only [revArrival] at h1
        push_cast at h1 ⊢
        nlinarith [hU.1]
      · left; left
        refine ⟨lt_of_not_ge h1, ?_⟩
        simp only [revArrival]
        push_cast
        nlinarith [hU.2]
  calc (n : ℕ∞) + tildeY h ξ n ω
      = (A ∪ ((fun i : ℤ => (n : ℤ) + i) '' Tset)).encard := by
        rw [Set.encard_union_eq hdisj, hA, hT]
    _ ≤ (Rset ∪ ((fun i : ℤ => (n : ℤ) + 1 - i) '' Yset) ∪ Gset).encard := encard_le_encard hsub
    _ ≤ (Rset ∪ ((fun i : ℤ => (n : ℤ) + 1 - i) '' Yset)).encard + Gset.encard :=
        encard_union_le _ _
    _ ≤ Rset.encard + ((fun i : ℤ => (n : ℤ) + 1 - i) '' Yset).encard + Gset.encard := by
        gcongr; exact encard_union_le _ _
    _ = _ := by rw [hY]; rfl
