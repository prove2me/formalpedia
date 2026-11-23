-- Prove2me | solution 1 for PI.FglPhSplit.Wk.allIn_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:24.165839+00:00
-- url     : https://prove2.me/submissions/dc17812d-503c-4ce3-bf62-f83dc6ababd1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit
variable {K : Type} [Field K]
namespace PI.FglPhSplit.Wk
theorem _root_.solution {W : Subring K} {σ : Type} : AllIn W (1 : MvPowerSeries σ K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact W.one_mem
  · exact W.zero_mem
end PI.FglPhSplit.Wk
