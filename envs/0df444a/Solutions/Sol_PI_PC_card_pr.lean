-- Prove2me | solution 1 for PI.PC.card_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:07.05492+00:00
-- url     : https://prove2.me/submissions/d0694be5-1f82-4128-9a85-b0017a6cc617

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real MeasureTheory Set
namespace PI.PC
theorem _root_.solution (y : ℝ) : (pr y).card = Nat.primeCounting ⌊y⌋₊ := by
  simp only [PI.pr, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]
  try (congr 1; ext p; simp)
end PI.PC
