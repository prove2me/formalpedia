-- Prove2me | solution 1 for SMHiggsPotential.quartic_bracket_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T09:31:22.446484+00:00
-- url     : https://prove2.me/submissions/3732cff3-c7f9-48f5-89a4-ef00279d1648

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs

open SMHiggsPotential

theorem solution (H φ0 p : ℝ) :
    H ^ 4 + φ0 ^ 4 + 4 * p ^ 2 + 4 * φ0 ^ 2 * p + 4 * H ^ 2 * p + 2 * φ0 ^ 2 * H ^ 2 =
      (H ^ 2 + φ0 ^ 2 + 2 * p) ^ 2 := by
  ring
