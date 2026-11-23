-- Prove2me | solution 1 for PI.AmpRootJacW.continuous_vM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:48.01337+00:00
-- url     : https://prove2.me/submissions/f1cc8f74-405b-4463-a749-11f2fcae699c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero

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
theorem _root_.solution : Continuous (vM S) := by
  unfold vM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const
end PI.AmpRootJacW
