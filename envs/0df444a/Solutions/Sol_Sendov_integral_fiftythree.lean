-- Prove2me | solution 1 for Sendov.integral_fiftythree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:09:07.490547+00:00
-- url     : https://prove2.me/submissions/2bf5e506-59ff-463f-8284-8ebc544e10e3

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree53Packed
import Theorems.Thm_Sendov_pev_Nmom53
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 1000000
open Sendov
namespace Sendov
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 53 α t ^ 24)
      = pev Nmom53 α / ((L53 : ℝ) * (2 * M 53 * (3 + α)) ^ 24) :=
  integral_moment_packed 53 24 (by norm_num) α hα L53 (by norm_num [L53]) Nmom53
    (by decide) (pev_Nmom53 α)
end Sendov
