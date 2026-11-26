-- Prove2me | solution 1 for Sendov.A_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:59:59.440036+00:00
-- url     : https://prove2.me/submissions/aa199340-de67-4e04-91bd-da9f71b77a08

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch
import Theorems.Thm_Sendov_M_mono
import Theorems.Thm_Sendov_M_pos


set_option autoImplicit false
open Sendov
variable {α t : ℝ}
namespace Sendov
theorem _root_.solution {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α) : A m α ≤ A n α := by
  have hMm : 0 < M m := M_pos hm
  have hMn : 0 < M n := lt_of_lt_of_le hMm (M_mono h)
  simp only [A]
  have : 2 * α / M n ≤ 2 * α / M m :=
    div_le_div_of_nonneg_left (by linarith) hMm (M_mono h)
  linarith
end Sendov
