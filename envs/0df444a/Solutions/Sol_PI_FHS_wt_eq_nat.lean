-- Prove2me | solution 1 for PI.FHS.wt_eq_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:59.962079+00:00
-- url     : https://prove2.me/submissions/5435f526-c3c6-4088-b16d-2fee1d3e5f8b

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg

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
theorem _root_.solution (α : σ →₀ ℕ) : wt α = ((α.prod fun _ k => k.factorial : ℕ) : ℂ) := by
  simp [wt, Finsupp.prod]
end PI.FHS
