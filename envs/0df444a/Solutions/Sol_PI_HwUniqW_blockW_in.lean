-- Prove2me | solution 1 for PI.HwUniqW.blockW_in
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:42:16.556907+00:00
-- url     : https://prove2.me/submissions/e5b88c2d-9a76-45c9-8cb5-39edd58c4388

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
theorem _root_.solution (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)} (hi : InB k r i)
    (hj : InB k r j) :
    blockW k r h i j = h ⟨i.val - r, by unfold InB at hi; omega⟩ ⟨j.val - r, by unfold InB at hj; omega⟩ := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : r ≤ j.val ∧ j.val < r + k := hj
  simp only [blockW]
  rw [dif_pos hi', dif_pos hj']
end PI.HwUniqW
