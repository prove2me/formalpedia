-- Prove2me | solution 1 for Sendov.rpow_le_rpow_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:07:21.628855+00:00
-- url     : https://prove2.me/submissions/5d178fdd-5300-4a09-a404-d8836450a6dd

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_Common_Rpow

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {x s t : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hts : t ≤ s) :
    x ^ s ≤ x ^ t :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hts
end Sendov
