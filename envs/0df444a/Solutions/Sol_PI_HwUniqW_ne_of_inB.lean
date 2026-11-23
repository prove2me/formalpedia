-- Prove2me | solution 1 for PI.HwUniqW.ne_of_inB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:09.395964+00:00
-- url     : https://prove2.me/submissions/43953112-c5f2-47db-a81e-1850e3ab5920

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
namespace PI.HwUniqW
theorem _root_.solution {i j : Fin (2 * r + k + 1)} (hi : InB k r i) (hj : ¬ InB k r j) : i ≠ j := by
  intro h
  subst h
  exact hj hi
end PI.HwUniqW
