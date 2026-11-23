-- Prove2me | solution 1 for PI.HwUniqW.blockW_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:52.990703+00:00
-- url     : https://prove2.me/submissions/6bde3c2d-c4e7-42ea-b13c-6f1381b3ab1d

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
theorem _root_.solution (a : Matrix (Fin k) (Fin k) ℂ) : (blockW k r a)ᴴ = blockW k r aᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : InB k r i <;> by_cases hj : InB k r j
  · rw [blockW_in a hj hi, blockW_in _ hi hj, Matrix.conjTranspose_apply]
  · rw [blockW_out a hj, blockW_in_out _ hi hj, if_neg (ne_of_inB hi hj).symm, star_zero]
  · rw [blockW_in_out a hj hi, blockW_out _ hi, if_neg (fun h => ne_of_inB hj hi h.symm), star_zero]
  · rw [blockW_out a hj, blockW_out _ hi]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg hij, if_neg (Ne.symm hij), star_zero]
end PI.HwUniqW
