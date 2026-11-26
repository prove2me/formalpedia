-- Prove2me | solution 1 for Section5BooleanFrame.amplitude_mgf_le
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:09:37.463532+00:00
-- url     : https://prove2.me/submissions/86ebc734-3078-4acb-b647-a3de3937363d

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
import Theorems.Thm_Section5BooleanFrame_amplitude_mgf
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem solution (u : ι → ℝ) (t : ℝ) :
    Section5BooleanFrame.average (fun x => Real.exp (t*Section5BooleanFrame.amplitude u x)) ≤
      Real.exp (t^2*(∑ i, u i^2)/2) := by
  rw [Section5BooleanFrame.amplitude_mgf]
  calc
    _ ≤ ∏ i, Real.exp ((t*u i)^2/2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact (Real.cosh_pos _).le
      · intro i _
        exact Real.cosh_le_exp_half_sq _
    _ = Real.exp (t^2*(∑ i, u i^2)/2) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [mul_pow,Finset.sum_div,Finset.mul_sum]
