-- Prove2me | solution 1 for PI.HwUniqW.fix_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:53:06.765295+00:00
-- url     : https://prove2.me/submissions/68d57af0-a1f2-4d44-93a0-600dad0984ce

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Theorems.Thm_PI_HwUniqW_block_mk
import Theorems.Thm_PI_HwUniqW_ne_of_inB
import Theorems.Thm_PI_HwUniqW_blockW_in
import Theorems.Thm_PI_HwUniqW_blockW_in_out
import Theorems.Thm_PI_HwUniqW_blockW_out
import Theorems.Thm_PI_HwUniqW_mem_UJset_allPos
import Theorems.Thm_PI_HwUniqW_unitary_of_blockW_mem
import Theorems.Thm_PI_HwUniqW_fix_col
import Theorems.Thm_PI_HwUniqW_fix_row

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
theorem _root_.solution {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : m ∈ UH (Hpk k r))
    (hm : FixEW k r m) : sub k r m ∈ UJset (allPos k) ∧ m = blockW k r (sub k r m) := by
  have hb : m = blockW k r (sub k r m) := by
    ext i j
    by_cases hj : InB k r j
    · by_cases hi : InB k r i
      · rw [blockW_in _ hi hj]
        show m i j = m (bl k r _) (bl k r _)
        rw [block_mk hi, block_mk hj]
      · rw [fix_row hU hm i j hi hj, blockW_out _ hi, if_neg (ne_of_inB hj hi).symm]
    · rw [fix_col hm j hj i]
      by_cases hi : InB k r i
      · rw [blockW_in_out _ hi hj, if_neg (ne_of_inB hi hj)]
      · rw [blockW_out _ hi]
  refine ⟨?_, hb⟩
  rw [mem_UJset_allPos]
  rw [hb] at hU
  exact unitary_of_blockW_mem hU
end PI.HwUniqW
