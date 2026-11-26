-- Prove2me | solution 1 for Sendov.integral_ninetyseven_47
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:09:22.307692+00:00
-- url     : https://prove2.me/submissions/5e6ae42d-4f34-4e56-9974-28bf81066fc5

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree97Packed
import Theorems.Thm_Sendov_pev_Nmom97_47
import Theorems.Thm_Sendov_integral_moment_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
namespace Sendov
theorem _root_.solution (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 97 α t ^ 47)
      = pev Nmom97_47 α / ((L97_47 : ℝ) * (2 * M 97 * (3 + α)) ^ 47) :=
  integral_moment_packed 97 47 (by norm_num) α hα L97_47 (by norm_num [L97_47]) Nmom97_47
    (by decide) (pev_Nmom97_47 α)
end Sendov
