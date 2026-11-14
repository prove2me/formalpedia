-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.sequential_phase_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:28:58.65172+00:00
-- url     : https://prove2.me/submissions/c802281a-06af-4147-9de4-fc50405ca209

import Mathlib
set_option autoImplicit false

theorem solution (f : ℕ → ℂ) (n : ℕ) (r : ℝ)
    (hstep : ∀ k < n, ‖f k - f (k+1)‖ ≤ r) :
    ‖f 0 - f n‖ ≤ n*r := by
  have hbound (k : ℕ) (hk : k ≤ n) : ‖f 0 - f k‖ ≤ k*r := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hkn : k < n := by omega
      have htri := norm_sub_le (f 0 - f k) (f (k+1) - f k)
      have heq : (f 0-f k)-(f (k+1)-f k) = f 0-f (k+1) := by abel
      rw [heq,norm_sub_rev (f (k+1)) (f k)] at htri
      have hb := ih (by omega)
      have hs := hstep k hkn
      rw [Nat.cast_succ]
      linarith
  exact hbound n (le_refl n)
