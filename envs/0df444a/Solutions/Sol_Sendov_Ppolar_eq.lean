-- Prove2me | solution 1 for Sendov.Ppolar_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:59:23.796266+00:00
-- url     : https://prove2.me/submissions/8700d748-f885-4b81-8eac-be71b3c046d1

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_Reduction_Setup

set_option autoImplicit false
open Sendov
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (a x t : ℝ) :
    Ppolar a x t = (a + t * (1 - a ^ 2) * x) ^ 2 + t ^ 2 * (1 - a ^ 2) ^ 2 * (1 - x ^ 2) := by
  simp only [Ppolar]; ring
end Sendov
