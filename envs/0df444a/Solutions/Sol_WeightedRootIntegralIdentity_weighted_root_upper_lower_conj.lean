-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weighted_root_upper_lower_conj
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-14T20:23:09.811971+00:00
-- url     : https://prove2.me/submissions/68e42416-32cf-49f6-b39c-6e81ffffbbb0

import Mathlib
open scoped BigOperators

theorem solution
    (n : ℕ) (a w : ℕ → ℝ) (x ε : ℝ) (hε : 0 < ε) :
    (∏ i ∈ Finset.range n,
        (((x : ℂ) - ε * Complex.I) - (a i : ℂ)) ^ (w i : ℂ)) /
          ((x : ℂ) - ε * Complex.I) =
      starRingEnd ℂ
        ((∏ i ∈ Finset.range n,
            (((x : ℂ) + ε * Complex.I) - (a i : ℂ)) ^ (w i : ℂ)) /
          ((x : ℂ) + ε * Complex.I)) := by
  rw [map_div₀, map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    have harg : (((x : ℂ) + ε * Complex.I) - (a i : ℂ)).arg ≠ Real.pi := by
      rw [Ne, Complex.arg_eq_pi_iff]
      push_neg
      intro _
      simp [ne_of_gt hε]
    simpa [sub_eq_add_neg] using
      (Complex.conj_cpow
        (((x : ℂ) + ε * Complex.I) - (a i : ℂ)) (w i : ℂ) harg)
  · simp [sub_eq_add_neg]
