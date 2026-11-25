-- Prove2me | solution 1 for PI.Mk.schurPoly_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:52:25.31134+00:00
-- url     : https://prove2.me/submissions/c49b7fbe-a19d-4bb4-a4a9-f652a73fb97e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_MinkowskiBoundOfSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Finset Polynomial
namespace PI.Mk
theorem _root_.solution (N ℓ m y : ℕ) (h1 : y ≠ 0) (h2 : y ≤ m) :
    (schurPoly N ℓ m).eval ((N : ℤ) - (ℓ : ℤ) * (y : ℤ)) = 0 := by
  unfold schurPoly
  rw [eval_prod]
  apply Finset.prod_eq_zero (i := y - 1) (Finset.mem_range.2 (by omega))
  have : y - 1 + 1 = y := by omega
  simp [this]
end PI.Mk
