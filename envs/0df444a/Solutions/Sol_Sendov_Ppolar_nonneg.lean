-- Prove2me | solution 1 for Sendov.Ppolar_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:00:00.721165+00:00
-- url     : https://prove2.me/submissions/328931f0-18b7-4e49-9210-1ec7bfe6ef17

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_Reduction_Setup
import Theorems.Thm_Sendov_Ppolar_eq

set_option autoImplicit false
open Sendov
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (hx : x ^ 2 ≤ 1) (a t : ℝ) : 0 ≤ Ppolar a x t := by
  rw [Ppolar_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by linarith))
end Sendov
