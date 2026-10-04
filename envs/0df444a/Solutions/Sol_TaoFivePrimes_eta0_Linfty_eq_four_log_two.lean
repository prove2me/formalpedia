-- Prove2me | solution 1 for TaoFivePrimes.eta0_Linfty_eq_four_log_two
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:14:30.966219+00:00
-- url     : https://prove2.me/submissions/d365e6c1-f890-4c59-99bc-1b08cb83612d

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open TaoFivePrimes

namespace TaoS12

/-- **Tao, equation (s1-2).**  `‖η₀‖_{L^∞(ℝ)} = 4 log 2`, attained at `t = 1/2`. -/
theorem eta0_sup : (∀ t : ℝ, eta0 t ≤ 4 * Real.log 2) ∧ eta0 (1/2) = 4 * Real.log 2 := by
  constructor
  · intro t
    unfold eta0
    split
    · have : max 0 (Real.log 2 - |Real.log (2*t)|) ≤ Real.log 2 :=
        max_le (Real.log_nonneg (by norm_num)) (by linarith [abs_nonneg (Real.log (2*t))])
      linarith
    · linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
  · unfold eta0
    rw [if_pos (by norm_num : (0:ℝ) < 1/2)]
    norm_num
    exact Real.log_nonneg (by norm_num)

end TaoS12

theorem solution :
    (∀ t : ℝ, TaoFivePrimes.eta0 t ≤ 4 * Real.log 2)
      ∧ TaoFivePrimes.eta0 (1/2) = 4 * Real.log 2 :=
  TaoS12.eta0_sup
