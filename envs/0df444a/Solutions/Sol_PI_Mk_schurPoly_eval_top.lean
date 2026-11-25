-- Prove2me | solution 1 for PI.Mk.schurPoly_eval_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:52:21.112798+00:00
-- url     : https://prove2.me/submissions/41d92788-f555-4e2d-9f4d-142cad8f91cc

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
theorem _root_.solution (N ℓ m : ℕ) :
    (schurPoly N ℓ m).eval (N : ℤ) = ((ℓ ^ m * m.factorial : ℕ) : ℤ) := by
  unfold schurPoly
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C, sub_sub_cancel]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Nat.cast_prod,
    Finset.prod_range_add_one_eq_factorial]
  push_cast
  ring
end PI.Mk
