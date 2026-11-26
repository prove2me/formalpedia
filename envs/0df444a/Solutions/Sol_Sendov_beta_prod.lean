-- Prove2me | solution 1 for Sendov.beta_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:58:57.232244+00:00
-- url     : https://prove2.me/submissions/8f6a31e5-3c07-4acf-8566-d37f9d1150a2

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}
namespace Sendov
theorem _root_.solution (n : ℕ) :
    (((n : ℝ) - 4) / 2 + 1) * (((n : ℝ) - 4) / 2 + 2) * (((n : ℝ) - 4) / 2 + 3)
        * (((n : ℝ) - 4) / 2 + 4)
      = ((n : ℝ) - 2) * (n : ℝ) * ((n : ℝ) + 2) * ((n : ℝ) + 4) / 16 := by
  ring
end Sendov
