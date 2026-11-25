-- Prove2me | solution 1 for PI.HwUniqW.inv_mul_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:55:43.641249+00:00
-- url     : https://prove2.me/submissions/6315e66d-f687-499f-ae46-e57aa76b135c

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Theorems.Thm_PI_HwUniqW_Hpk_mul_self

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
theorem _root_.solution {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
  have h : gᴴ * (Hpk k r * g) = Hpk k r := by
    rw [← Matrix.mul_assoc]
    exact hg
  simp only [Matrix.mul_assoc]
  rw [h, Hpk_mul_self]
end PI.HwUniqW
