-- Prove2me | solution 1 for Sendov.integral_ninetyseven_46
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:09:18.302356+00:00
-- url     : https://prove2.me/submissions/f4b8a2d9-2993-48fe-acb6-1c252c39da10

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree97Packed
import Theorems.Thm_Sendov_pev_Nmom97_46
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
namespace Sendov
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 97 α t ^ 46)
      = pev Nmom97_46 α / ((L97_46 : ℝ) * (2 * M 97 * (3 + α)) ^ 46) :=
  integral_moment_packed 97 46 (by norm_num) α hα L97_46 (by norm_num [L97_46]) Nmom97_46
    (by decide) (pev_Nmom97_46 α)
end Sendov
