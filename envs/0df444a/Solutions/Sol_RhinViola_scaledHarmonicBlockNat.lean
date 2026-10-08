-- Prove2me | solution 1 for RhinViola.scaledHarmonicBlockNat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:55:08.505885+00:00
-- url     : https://prove2.me/submissions/6bdc3135-435a-4898-a08c-75e9bc3cff49

import Mathlib
open scoped BigOperators

theorem solution
    (D h d : ℕ) (hd : 0 < d) (hdD : d ∣ D)
    (hdiv : ∀ j : ℕ, j < d → h + j + 1 ∣ D) :
    (D : ℝ) ^ 2 *
        ((1 : ℝ) / (d : ℝ) *
          Finset.sum (Finset.range d) (fun j : ℕ =>
            (1 : ℝ) / (((h + j + 1 : ℕ) : ℝ)))) =
      ((Finset.sum (Finset.range d) (fun j : ℕ =>
          (D / d) * (D / (h + j + 1))) : ℕ) : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjd : j < d := Finset.mem_range.mp hj
  have hk : ((h + j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_mul, Nat.cast_div hdD hd0, Nat.cast_div (hdiv j hjd) hk]
  field_simp
