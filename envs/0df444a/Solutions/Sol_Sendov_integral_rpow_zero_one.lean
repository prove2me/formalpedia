-- Prove2me | solution 1 for Sendov.integral_rpow_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:08.811518+00:00
-- url     : https://prove2.me/submissions/904a9992-9a03-40d5-bccc-add58d5ac005

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_Common_Rpow

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {s : ℝ} (hs : -1 < s) :
    (∫ x in (0 : ℝ)..1, x ^ s) = 1 / (s + 1) := by
  rw [integral_rpow (Or.inl hs), Real.one_rpow, Real.zero_rpow (by linarith)]
  ring
end Sendov
