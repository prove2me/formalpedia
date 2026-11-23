-- Prove2me | solution 1 for PI.HwUniqW.Hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:54.160837+00:00
-- url     : https://prove2.me/submissions/15d7508f-8f90-4b9d-8e2b-082aa0910f46

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Theorems.Thm_PI_HwUniqW_piI_val

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
theorem _root_.solution (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = piI k r i then epsI k r i else 0 := by
  have hj : j = piI k r i ↔
      j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := by
    rw [Fin.ext_iff, piI_val]
  have := i.isLt
  have := j.isLt
  unfold Hpk epsI
  simp only [hj, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | norm_num
end PI.HwUniqW
