-- Prove2me | solution 1 for PI.Mk.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:07.187002+00:00
-- url     : https://prove2.me/submissions/c335d52d-5a02-4d8b-b23f-f2b1d41452ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Finset
namespace PI.Mk
theorem _root_.solution (N p i : ℕ) : N / (p ^ i * (p - 1)) = (N / (p - 1)) / p ^ i := by
  rw [mul_comm, Nat.div_div_eq_div_mul]
end PI.Mk
