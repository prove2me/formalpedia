-- Prove2me | solution 1 for Sendov.continuous_Ppolar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:52:28.979901+00:00
-- url     : https://prove2.me/submissions/0e3f67f1-4e7a-4e4f-97ec-4b9438baf58e

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_Reduction_Setup

set_option autoImplicit false
open Sendov
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (a x : ℝ) : Continuous fun t : ℝ => Ppolar a x t := by
  simp only [Ppolar]; fun_prop
end Sendov
