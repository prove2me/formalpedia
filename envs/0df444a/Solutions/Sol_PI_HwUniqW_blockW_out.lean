-- Prove2me | solution 1 for PI.HwUniqW.blockW_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:42:25.086439+00:00
-- url     : https://prove2.me/submissions/ea7f0bee-a259-4b2d-9e42-040a7521b8fa

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
theorem _root_.solution (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)} (hi : ¬ InB k r i) :
    blockW k r h i j = if i = j then 1 else 0 := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  simp only [blockW]
  rw [dif_neg hi']
end PI.HwUniqW
