-- Prove2me | solution 1 for ProbabilityTheory.LevyKhintchineTriple.exponent_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:08:16.536689+00:00
-- url     : https://prove2.me/submissions/b0b34650-fc09-4800-b5f0-b451a7fc47de

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex

/-- Vanishing of the Lévy–Khintchine exponent at frequency zero. -/
theorem solution (T : LevyKhintchineTriple) : T.exponent 0 = 0 := by
  simp [LevyKhintchineTriple.exponent, levyCompensatedIntegrand]
