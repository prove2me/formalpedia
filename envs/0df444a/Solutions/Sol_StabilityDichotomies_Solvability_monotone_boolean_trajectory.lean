-- Prove2me | solution 1 for StabilityDichotomies.Solvability.monotone_boolean_trajectory
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:56:57.783228+00:00
-- url     : https://prove2.me/submissions/36d09e6e-3413-4f21-b0e9-6631e17f9a20

import Mathlib
noncomputable section
open scoped Classical BigOperators

theorem solution {V : Type} [Fintype V]
    (U : Finset V) (n : ℕ) (f : ℕ → V → Bool)
    (hmono : ∀ k < n, ∀ v ∈ U, f k v ≤ f (k + 1) v) :
    (∑ k ∈ Finset.range n, ∑ v ∈ U,
      (if f k v ≠ f (k + 1) v then (1 : ℤ) else 0)) ≤ U.card := by
  have hstep : ∀ k < n, ∀ v ∈ U,
      (if f k v ≠ f (k + 1) v then (1 : ℤ) else 0) =
      ((f (k + 1) v).toNat : ℤ) - (f k v).toNat := by
    intro k hk v hv
    have hm := hmono k hk v hv
    cases h0 : f k v <;> cases h1 : f (k + 1) v <;> simp_all [Bool.toNat]
    exact (by decide : ¬ ((true : Bool) ≤ false)) hm
  calc
    _ = ∑ v ∈ U, ∑ k ∈ Finset.range n,
        (if f k v ≠ f (k + 1) v then (1 : ℤ) else 0) := Finset.sum_comm
    _ = ∑ v ∈ U, (((f n v).toNat : ℤ) - (f 0 v).toNat) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← Finset.sum_range_sub (fun k => ((f k v).toNat : ℤ)) n]
      apply Finset.sum_congr rfl
      intro k hk
      exact hstep k (Finset.mem_range.mp hk) v hv
    _ ≤ ∑ _v ∈ U, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro v hv
      cases f n v <;> cases f 0 v <;> norm_num [Bool.toNat]
    _ = U.card := by simp
