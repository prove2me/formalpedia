-- Prove2me | solution 1 for PI.AmpRootJacW.continuous_hSh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:11.846814+00:00
-- url     : https://prove2.me/submissions/0f395456-efae-4465-af3c-9c224aa31f80

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
import Theorems.Thm_PI_AmpRootJacW_continuous_vM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
variable (S : Finset (Fin n × Fin n))
namespace PI.AmpRootJacW
theorem _root_.solution (q : S) : Continuous (hSh S q) := by
  unfold hSh
  refine Continuous.neg (continuous_finset_sum _ (fun m _ => ?_))
  have h1 : Continuous (fun v : S → ℂ => (-vM S v) ^ (m + 1 + 1)) := ((continuous_vM S).neg).pow _
  exact h1.matrix_elem q.1.1 q.1.2
end PI.AmpRootJacW
