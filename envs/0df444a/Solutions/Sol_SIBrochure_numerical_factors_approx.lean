-- Prove2me | solution 1 for SIBrochure.numerical_factors_approx
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T22:53:24.729408+00:00
-- url     : https://prove2.me/submissions/7b4104a8-aac5-4882-9e13-85a3b05f4e9f

import Mathlib
import Definitions.Def_SIBrochure_units

set_option autoImplicit false

open SIBrochure in
theorem solution :
    |(9192631770 / 299792458 : ℝ) - 30.663319| ≤ 5e-7 ∧
    |(299792458 : ℝ) ^ 2 / (6.62607015e-34 * 9192631770) - 1.4755214e40| ≤ 5e32 ∧
    |(1 / (9192631770 * 1.602176634e-19) : ℝ) - 6.789687e8| ≤ 5e1 ∧
    |(1.380649e-23 / (6.62607015e-34 * 9192631770) : ℝ) - 2.2666653| ≤ 5e-8 ∧
    |(1 / (6.62607015e-34 * (9192631770 : ℝ) ^ 2 * 683)) - 2.614830e10| ≤ 5e3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> norm_num
