-- Prove2me | solution 1 for PI.FHS.wt_pos_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:34.943451+00:00
-- url     : https://prove2.me/submissions/1b8cb08e-a4f5-4dc4-a19a-a79362ad7ec6

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
theorem _root_.solution (α : σ →₀ ℕ) : 0 < (α.prod fun _ k => k.factorial : ℕ) := by
  unfold Finsupp.prod
  exact Finset.prod_pos fun i _ => Nat.factorial_pos _
end PI.FHS
