-- Prove2me | solution 1 for Sendov.continuous_lowX_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:55:25.473069+00:00
-- url     : https://prove2.me/submissions/a99a05ae-200b-4539-88ee-de32c5e6de72

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a : ℝ) (m : ℕ) : Continuous fun t : ℝ => lowX a t ^ m := by
  simp only [lowX]
  fun_prop
end Sendov
