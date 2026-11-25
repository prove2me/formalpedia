-- Prove2me | solution 1 for PI.WwEvalWork.Lsum_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:18:20.855687+00:00
-- url     : https://prove2.me/submissions/d77b159b-3123-4cb5-a7ab-48ac329d86b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwEvalWork
open MvPolynomial
variable {σ K : Type*} [CommRing K]
namespace PI.WwEvalWork
theorem _root_.solution (w : (σ →₀ ℕ) → K) : Lsum w (0 : MvPolynomial σ K) = 0 := by
  simp [Lsum]
end PI.WwEvalWork
