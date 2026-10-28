-- Prove2me | solution 1 for WilliamsonShmoys.face_certificate_of_edge_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:38:30.892985+00:00
-- url     : https://prove2.me/submissions/9cfdc058-7818-4b15-b440-ec9fc5ec5981

import Mathlib

set_option autoImplicit false

theorem S183fc (n e : ℕ) (hL : n ≤ e + 1) (hU : e + 6 ≤ 3 * n) :
    ∃ (m : Nat) (degree : Fin m → ℤ),
      (n : ℤ) - (e : ℤ) + m = 2 ∧ (∑ f : Fin m, degree f) = 2 * (e : ℤ) ∧ (∀ f, 3 ≤ degree f) := by
  obtain ⟨k, hk⟩ : ∃ k, e + 2 - n = k + 1 := ⟨e + 1 - n, by omega⟩
  refine ⟨k + 1, Fin.cases (2 * (e : ℤ) - 3 * k) (fun _ => 3), ?_, ?_, ?_⟩
  · push_cast; omega
  · rw [Fin.sum_univ_succ]; simp; ring
  · intro f
    refine Fin.cases ?_ (fun _ => ?_) f
    · simp; omega
    · simp

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hLower : Fintype.card V <= K.edgeSet.ncard + 1)
    (hUpper : K.edgeSet.ncard + 6 <= 3 * Fintype.card V) :
    ∃ (m : Nat) (degree : Fin m → ℤ),
      (Fintype.card V : ℤ) - (K.edgeSet.ncard : ℤ) + m = 2 ∧
      (∑ f : Fin m, degree f) = 2 * (K.edgeSet.ncard : ℤ) ∧
      (∀ f, 3 <= degree f) := by
  exact S183fc _ _ hLower hUpper
