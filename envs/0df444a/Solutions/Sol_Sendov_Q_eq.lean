-- Prove2me | solution 1 for Sendov.Q_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:07.101632+00:00
-- url     : https://prove2.me/submissions/1a6e2c36-b0cc-4efc-acd6-79d60ab111ae

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (n : ℕ) (α t : ℝ) :
    Q n α t = (1 - c n α * t) ^ 2 + (A n α - c n α ^ 2) * t ^ 2 := by
  simp only [Q]
  ring
end Sendov
