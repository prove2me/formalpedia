-- Prove2me | solution 1 for PI.PC.gg_1024_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:33.135387+00:00
-- url     : https://prove2.me/submissions/bb072ac7-6aeb-4319-8aa5-79ddf03e8668

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
theorem _root_.solution : 0 ≤ gg 1024 := by
  have hl : 0 < log (1024 : ℝ) := Real.log_pos (by norm_num)
  have h1 : 0 ≤ (1024 : ℝ) / log 1024 ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
  unfold gg
  linarith
end PI.PC
