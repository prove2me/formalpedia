-- Prove2me | solution 1 for PI.HwUniqW.conj_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:04:42.070737+00:00
-- url     : https://prove2.me/submissions/74a0b92e-2db1-41b3-8e06-f11e7b32b472

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Theorems.Thm_PI_HwUniqW_inv_fix
import Theorems.Thm_PI_HwUniqW_frame_inv_mulVec_negativeVector
import Theorems.Thm_PI_HwUniqW_fix_of_smul
import Theorems.Thm_PI_HwUniqW_sqrtT_ne

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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hT : 0 < Tz k r z) (hg : IsFrameW k r z g) (hx : x ∈ UWset k r z) : FixEW k r (g⁻¹ * x * g) := by
  have hg0 := hg
  obtain ⟨hgU, hge, hgz⟩ := hg0
  obtain ⟨-, hxe, hxz⟩ := hx
  unfold FixEW
  refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hge a).1, (hxe a).1, inv_fix hgU (hge a).1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hge a).2, (hxe a).2, inv_fix hgU (hge a).2]
  · apply fix_of_smul (sqrtT_ne hT)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgz, hxz, frame_inv_mulVec_negativeVector hg]
end PI.HwUniqW
