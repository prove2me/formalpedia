-- Prove2me | solution 1 for WorkbookCorrected.plus_70623
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:59:34.916902+00:00
-- url     : https://prove2.me/submissions/c1d5d48e-f78e-46b0-a02b-ddb0eec7fd59

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (n : ℕ) (hn : 0<n) (hnc : ¬ ∃ k : ℕ, k^3=n)
    (r : ℝ) (hr : 0 ≤ r) (he : r^3=(n:ℝ)) : r-(⌊r⌋₊:ℝ) > 1/(3*r^2) := by
  let k : ℕ := ⌊r⌋₊
  have hk : (k:ℝ) ≤ r := Nat.floor_le hr
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hkpow : (k:ℝ)^3 ≤ r^3 := pow_le_pow_left₀ hk0 hk 3
  have hkn : k^3 ≤ n := by exact_mod_cast (show (k:ℝ)^3 ≤ (n:ℝ) by linarith only [hkpow,he])
  have hkne : k^3 ≠ n := by intro hh; exact hnc ⟨k,hh⟩
  have hgap : (k:ℝ)^3+1 ≤ (n:ℝ) := by exact_mod_cast (show k^3+1 ≤ n by omega)
  have hstrict : (k:ℝ) < r := by
    by_contra hh
    have hh2 : r=(k:ℝ) := le_antisymm (le_of_not_gt hh) hk
    rw [hh2] at he
    apply hkne
    exact_mod_cast he
  have hrp : 0<r := lt_of_le_of_lt hk0 hstrict
  have hd : 0<r-(k:ℝ) := sub_pos.mpr hstrict
  have hp := mul_pos (sq_pos_of_pos hd) (show 0<2*r+(k:ℝ) by linarith only [hrp,hk0])
  have hv : 1 < (r-(k:ℝ))*(3*r^2) := by nlinarith only [hp,hgap,he]
  exact (div_lt_iff₀ (show 0<3*r^2 by positivity)).mpr hv
example : (∀ (n : ℕ) (hn : 0<n) (hnc : ¬ ∃ k : ℕ, k^3=n)
    (r : ℝ) (hr : 0 ≤ r) (he : r^3=(n:ℝ)), r-(⌊r⌋₊:ℝ) > 1/(3*r^2)) := @solution
#print axioms solution
