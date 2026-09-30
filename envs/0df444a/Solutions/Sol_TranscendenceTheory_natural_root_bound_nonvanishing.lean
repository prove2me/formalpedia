-- Prove2me | solution 1 for TranscendenceTheory.natural_root_bound_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T03:49:19.861087+00:00
-- url     : https://prove2.me/submissions/ee0147c5-d5db-45db-b1b9-b8d3f010f4ad

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Preimage

open scoped Classical

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (p : Polynomial R) (N : ℕ) (hdegree : p.natDegree ≤ N) :
    let B : Finset ℕ := p.roots.toFinset.preimage (Nat.cast : ℕ → R)
      Nat.cast_injective.injOn
    B.card ≤ N ∧
    ((∃ n : Fin (N + 1), p.eval (n.val : R) ≠ 0) ↔
      ∃ n : Fin (B.card + 1), p.eval (n.val : R) ≠ 0) := by
  classical
  dsimp only
  let B : Finset ℕ := p.roots.toFinset.preimage (Nat.cast : ℕ → R)
    Nat.cast_injective.injOn
  have hB : B.card ≤ N := by
    calc
      B.card = (p.roots.toFinset.filter (fun x => x ∈ Set.range (Nat.cast : ℕ → R))).card :=
        Finset.card_preimage _ _ _
      _ ≤ p.roots.toFinset.card := Finset.card_filter_le _ _
      _ ≤ p.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ ≤ N := hdegree
  refine ⟨hB, ?_⟩
  constructor
  · rintro ⟨n, hn⟩
    have hp : p ≠ 0 := by
      intro hz
      simp only [hz, Polynomial.eval_zero, ne_eq, not_true_eq_false] at hn
    obtain ⟨r, hrange, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := B) (t := Finset.range (B.card + 1)) (by simp)
    refine ⟨⟨r, Finset.mem_range.mp hrange⟩, ?_⟩
    intro hzero
    apply hr
    change r ∈ p.roots.toFinset.preimage (Nat.cast : ℕ → R) Nat.cast_injective.injOn
    rw [Finset.mem_preimage, Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact hzero
  · rintro ⟨n, hn⟩
    let n' : Fin (N + 1) := ⟨n.val, n.isLt.trans_le (Nat.add_le_add_right hB 1)⟩
    exact ⟨n', hn⟩
