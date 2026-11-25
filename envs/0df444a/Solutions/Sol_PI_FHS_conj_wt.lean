-- Prove2me | solution 1 for PI.FHS.conj_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:58.156144+00:00
-- url     : https://prove2.me/submissions/b08b4b19-8eb5-4b4c-a75d-06eaa1b6c8a4

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Theorems.Thm_PI_FHS_wt_eq_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}
namespace PI.FHS
theorem _root_.solution (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α := by
  rw [wt_eq_nat, map_natCast]
end PI.FHS
