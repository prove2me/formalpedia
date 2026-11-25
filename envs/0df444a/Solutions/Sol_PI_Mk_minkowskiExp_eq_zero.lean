-- Prove2me | solution 1 for PI.Mk.minkowskiExp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:51:51.684848+00:00
-- url     : https://prove2.me/submissions/e9faa3a7-0aed-420a-beaf-7f269a64f5e8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_Assemble
import Theorems.Thm_PI_Mk_term_eq

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
theorem _root_.solution (N p : ℕ) (hp : N + 2 ≤ p) : PI.minkowskiExp N p = 0 := by
  unfold PI.minkowskiExp
  apply Finset.sum_eq_zero
  intro i _
  have h0 : N / (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
  rw [term_eq, h0, Nat.zero_div]
end PI.Mk
