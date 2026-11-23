-- Prove2me | solution 1 for PI.HwUniqW.epsI_in
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:53.716431+00:00
-- url     : https://prove2.me/submissions/0dd76188-90a6-4bf9-8927-e26f244e4eb8

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
theorem _root_.solution {i : Fin (2 * r + k + 1)} (hi : InB k r i) : epsI k r i = 1 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  unfold epsI
  rw [if_neg (by omega)]
end PI.HwUniqW
