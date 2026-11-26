-- Prove2me | solution 1 for Sendov.rpow_add_nat_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:19.864604+00:00
-- url     : https://prove2.me/submissions/9e1ed8e3-b7a9-4cba-ac2b-14f6e08e6be1

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_Common_Rpow

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {x : ℝ} (hx : 0 < x) (s : ℝ) (m : ℕ) :
    x ^ (s + (m : ℝ)) = x ^ s * x ^ m := by
  rw [Real.rpow_add hx, Real.rpow_natCast]
end Sendov
