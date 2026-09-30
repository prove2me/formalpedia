-- Prove2me | solution 1 for collatz_generalization_5x1
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:19:13.240454+00:00
-- url     : https://prove2.me/submissions/2475a0ff-f9b9-4a26-b747-1dd920764873

import Mathlib

set_option autoImplicit false

theorem solution :
    ¬ (∀ n : ℕ, 1 ≤ n →
      ∃ k : ℕ, Nat.rec n (fun _ m =>
        if m % 2 = 0 then m / 2 else (5 * m + 1) / 2) k = 1) := by
  let step : ℕ → ℕ := fun m =>
    if m % 2 = 0 then m / 2 else (5 * m + 1) / 2
  let cycle : Finset ℕ := {13, 33, 83, 208, 104, 52, 26}
  have closed (m : ℕ) (hm : m ∈ cycle) : step m ∈ cycle := by
    simp only [cycle, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [step, cycle]
  have stays (k : ℕ) : Nat.rec 13 (fun _ m => step m) k ∈ cycle := by
    induction k with
    | zero => norm_num [cycle]
    | succ k ih => exact closed _ ih
  intro h
  obtain ⟨k, hk⟩ := h 13 (by norm_num)
  have hm := stays k
  change Nat.rec 13 (fun _ m =>
    if m % 2 = 0 then m / 2 else (5 * m + 1) / 2) k ∈ cycle at hm
  rw [hk] at hm
  norm_num [cycle] at hm

#print axioms solution
