-- Prove2me | solution 1 for RH.Transport.SupportedMass.half_decay_exponent_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:03.80021+00:00
-- url     : https://prove2.me/submissions/a8da1abe-16bc-412b-a3e5-88d35ddb5497

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
import Theorems.Thm_RH_Transport_Geometry_positive_part_le_subset


set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section
namespace RH.Transport.SupportedMass
theorem _root_.solution {p d : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) :
    -d / 2 + max 0 (5 * Geometry.ell p - 1 + d) / 8 ≤ 0 := by
  have hm := Geometry.positive_part_le_subset hp hd
  linarith
end RH.Transport.SupportedMass
