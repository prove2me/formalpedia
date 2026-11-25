-- Prove2me | solution 1 for PI.SqfRootsInj.W.log_cast_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:21.441244+00:00
-- url     : https://prove2.me/submissions/178e8f88-ffbd-4a36-a5bc-3f85114d2b47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_RpowQuarterPowFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution (n g k : ℕ) (hn : n ≠ 0) (h : n ≤ g ^ k) :
    Real.log n ≤ k * Real.log g := by
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) (by exact_mod_cast h)
end PI.SqfRootsInj.W
