-- Prove2me | solution 1 for PI.HwUniqW.UW_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:10:50.463185+00:00
-- url     : https://prove2.me/submissions/f3f14b50-8e43-4f52-aef1-611aa8798e39

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Theorems.Thm_PI_HwUniqW_conj_UH
import Theorems.Thm_PI_HwUniqW_conj_fix
import Theorems.Thm_PI_HwUniqW_fix_block
import Theorems.Thm_PI_HwUniqW_mul_inv_UH


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
    (hT : 0 < Tz k r z) (hg : IsFrameW k r z g) (hx : x ∈ UWset k r z) :
    ∃ h ∈ UJset (allPos k), g⁻¹ * x * g = blockW k r h ∧ x = g * blockW k r h * g⁻¹ := by
  obtain ⟨hU, hb⟩ := fix_block (conj_UH hg hx) (conj_fix hT hg hx)
  refine ⟨_, hU, hb, ?_⟩
  rw [← hb]
  calc x = (g * g⁻¹) * x * (g * g⁻¹) := by rw [mul_inv_UH hg.1, Matrix.one_mul, Matrix.mul_one]
    _ = g * (g⁻¹ * x * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
end PI.HwUniqW
