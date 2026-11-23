-- Prove2me | solution 1 for PI.HwUniqW.blockW_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:53.110804+00:00
-- url     : https://prove2.me/submissions/f440e8d5-257b-41e2-914c-16764099f727

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Theorems.Thm_PI_HwUniqW_ne_of_inB
import Theorems.Thm_PI_HwUniqW_blockW_in
import Theorems.Thm_PI_HwUniqW_blockW_in_out
import Theorems.Thm_PI_HwUniqW_blockW_out

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
theorem _root_.solution : blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  ext i j
  by_cases hi : InB k r i
  · by_cases hj : InB k r j
    · rw [blockW_in _ hi hj, Matrix.one_apply, Matrix.one_apply]
      have hi' : r ≤ i.val ∧ i.val < r + k := hi
      have hj' : r ≤ j.val ∧ j.val < r + k := hj
      by_cases hij : i = j
      · subst hij
        simp
      · rw [if_neg hij, if_neg]
        intro h
        apply hij
        have h2 := congrArg Fin.val h
        change i.val - r = j.val - r at h2
        exact Fin.ext (by omega)
    · rw [blockW_in_out _ hi hj, Matrix.one_apply, if_neg (ne_of_inB hi hj)]
  · rw [blockW_out _ hi, Matrix.one_apply]
end PI.HwUniqW
