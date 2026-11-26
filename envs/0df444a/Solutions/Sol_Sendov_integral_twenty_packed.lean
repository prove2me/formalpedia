-- Prove2me | solution 1 for Sendov.integral_twenty_packed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:20:16.954242+00:00
-- url     : https://prove2.me/submissions/3d3fe59a-e76f-4442-915e-e3a53b742be6

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20Packed
import Theorems.Thm_Sendov_Nmom20_eq
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 100000
open Sendov
namespace Sendov
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 20 α t ^ 8)
      = pev Nmom20 α / ((L20 : ℝ) * (2 * M 20 * (3 + α)) ^ 8) :=
  integral_moment_packed 20 8 (by norm_num) α hα L20 (by norm_num [L20]) Nmom20
    (by decide) (by rw [Nmom20_eq])
end Sendov
