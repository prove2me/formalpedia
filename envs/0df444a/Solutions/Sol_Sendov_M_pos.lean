-- Prove2me | solution 1 for Sendov.M_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:38.645234+00:00
-- url     : https://prove2.me/submissions/db73eea4-6cda-41a6-acd8-cd08cc5bbe67

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) : 0 < M n := by
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [M]
  linarith
end Sendov
