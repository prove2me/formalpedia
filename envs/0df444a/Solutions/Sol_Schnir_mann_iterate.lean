-- Prove2me | solution 1 for Schnir.mann_iterate
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T08:05:15.230017+00:00
-- url     : https://prove2.me/submissions/6d853dd7-2bc6-4b59-95b2-58a4513772e1

import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Tactic.Linarith
import Theorems.Thm_Schnir_mann

/-!
# Iterated Mann: sigma(kA) >= min(1, k sigma(A))

`Schnir.mann` (Mann's theorem, proved on this platform) iterated: the Schnirelmann
density of the set of sums of exactly `k` elements of `A` is at least
`min(1, k * sigma A)`. This is the form the density iteration consumes.
-/

open Finset Pointwise Classical

/-- `min 1 ·` is monotone. -/
theorem min_one_mono {x y : ℝ} (h : x ≤ y) : min 1 x ≤ min 1 y := by
  rcases le_total 1 x with hx | hx
  · rw [min_eq_left hx]; exact le_min (le_refl 1) (hx.trans h)
  · rw [min_eq_right hx]; exact le_min hx h

namespace MannIter

/-- `iterA A k` = the set of sums of exactly `k` elements of `A` (with multiplicity). -/
def iterA (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ t : Multiset ℕ, t.card = k ∧ (∀ x ∈ t, x ∈ A) ∧ t.sum = n}

theorem zero_mem_iterA (A : Set ℕ) (hA0 : 0 ∈ A) (k : ℕ) : 0 ∈ iterA A k := by
  refine ⟨Multiset.replicate k 0, Multiset.card_replicate k 0, ?_, ?_⟩
  · intro x hx
    rw [(Multiset.mem_replicate.1 hx).2]
    exact hA0
  · rw [Multiset.sum_replicate]
    simp

theorem step_subset (A : Set ℕ) (k : ℕ) : iterA A k + A ⊆ iterA A (k + 1) := by
  intro x hx
  rw [Set.mem_add] at hx
  obtain ⟨y, hy, a, haA, hyx⟩ := hx
  obtain ⟨t, htk, htm, hts⟩ := hy
  refine ⟨Multiset.cons a t, by rw [Multiset.card_cons, htk], ?_, ?_⟩
  · intro x' hx'
    rw [Multiset.mem_cons] at hx'
    rcases hx' with rfl | hx'
    · exact haA
    · exact htm x' hx'
  · rw [Multiset.sum_cons]
    omega

end MannIter

open Pointwise Classical

open Pointwise Classical in
/-- Mann's theorem iterated: `sigma(kA) >= min(1, k sigma(A))`. -/
theorem solution (A : Set ℕ) (hA0 : 0 ∈ A) (k : ℕ) :
    min 1 ((k : ℝ) * schnirelmannDensity A) ≤
      schnirelmannDensity {n | ∃ t : Multiset ℕ, t.card = k ∧ (∀ x ∈ t, x ∈ A) ∧ t.sum = n} := by
  induction k with
  | zero =>
    have h0 : (((0 : ℕ) : ℝ) * schnirelmannDensity A) = 0 := by simp
    rw [h0]
    exact le_trans (min_le_right 1 0) schnirelmannDensity_nonneg
  | succ k IH =>
    have h0k : 0 ∈ MannIter.iterA A k := MannIter.zero_mem_iterA A hA0 k
    have hmann := Schnir.mann (MannIter.iterA A k) A h0k hA0
    have hsub : schnirelmannDensity (MannIter.iterA A k + A)
        ≤ schnirelmannDensity (MannIter.iterA A (k + 1)) :=
      schnirelmannDensity_le_of_subset (MannIter.step_subset A k)
    have hminstep : min 1 (((k + 1 : ℕ) : ℝ) * schnirelmannDensity A)
        ≤ min 1 (min 1 ((k : ℝ) * schnirelmannDensity A) + schnirelmannDensity A) := by
      have hσ : (0 : ℝ) ≤ schnirelmannDensity A := schnirelmannDensity_nonneg
      have hc : (((k + 1 : ℕ) : ℝ) * schnirelmannDensity A)
          = (k : ℝ) * schnirelmannDensity A + schnirelmannDensity A := by
        push_cast; ring
      rcases le_total 1 ((k : ℝ) * schnirelmannDensity A) with h | h
      · have h1 : min 1 (((k + 1 : ℕ) : ℝ) * schnirelmannDensity A) = 1 := by
          apply min_eq_left; rw [hc]; linarith
        have h2 : min 1 (min 1 ((k : ℝ) * schnirelmannDensity A) + schnirelmannDensity A) = 1 := by
          rw [min_eq_left h]; apply min_eq_left; linarith
        rw [h1, h2]
      · have hr : min 1 ((k : ℝ) * schnirelmannDensity A) = (k : ℝ) * schnirelmannDensity A :=
          min_eq_right h
        rw [hc, hr]
    calc min 1 (((k + 1 : ℕ) : ℝ) * schnirelmannDensity A)
        ≤ min 1 (min 1 ((k : ℝ) * schnirelmannDensity A) + schnirelmannDensity A) := hminstep
      _ ≤ min 1 (schnirelmannDensity (MannIter.iterA A k) + schnirelmannDensity A) :=
          min_one_mono (add_le_add IH (le_refl _))
      _ ≤ schnirelmannDensity (MannIter.iterA A k + A) := hmann
      _ ≤ schnirelmannDensity (MannIter.iterA A (k + 1)) := hsub
