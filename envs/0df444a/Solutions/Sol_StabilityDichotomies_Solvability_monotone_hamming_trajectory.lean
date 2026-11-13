-- Prove2me | solution 1 for StabilityDichotomies.Solvability.monotone_hamming_trajectory
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:58:43.207551+00:00
-- url     : https://prove2.me/submissions/93aeb0bf-a000-49ce-92b4-c497aecc7f58

import Mathlib
noncomputable section
open scoped Classical BigOperators

private theorem flips_bound {V : Type} [Fintype V]
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

theorem solution {V : Type} [Fintype V]
    (U : Finset V) (n : ℕ) (f : ℕ → V → Bool)
    (hmono : ∀ k < n, ∀ v ∈ U, f k v ≤ f (k + 1) v)
    (hsupport : ∀ k < n, ∀ v ∉ U, f k v = f (k + 1) v) :
    (∑ k ∈ Finset.range n, hammingDist (f k) (f (k + 1))) ≤ U.card := by
  have hcount : ∀ k < n,
      (hammingDist (f k) (f (k + 1)) : ℤ) =
        ∑ v ∈ U, (if f k v ≠ f (k + 1) v then (1 : ℤ) else 0) := by
    intro k hk
    rw [hammingDist, ← Finset.sum_boole (fun v => f k v ≠ f (k + 1) v) Finset.univ]
    symm
    apply Finset.sum_subset (Finset.subset_univ U)
    intro v hv hnot
    simp [hsupport k hk v hnot]
  have hb := flips_bound U n f hmono
  have heq : (∑ k ∈ Finset.range n, (hammingDist (f k) (f (k + 1)) : ℤ)) =
      ∑ k ∈ Finset.range n, ∑ v ∈ U,
        (if f k v ≠ f (k + 1) v then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hcount k (Finset.mem_range.mp hk)
  rw [← heq] at hb
  exact_mod_cast hb
