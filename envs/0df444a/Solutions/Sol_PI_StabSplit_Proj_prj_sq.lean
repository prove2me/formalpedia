-- Prove2me | solution 1 for PI.StabSplit.Proj.prj_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:42.552522+00:00
-- url     : https://prove2.me/submissions/9588a7b4-4674-4764-963c-39b93f03634e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL
import Theorems.Thm_PI_StabSplit_Proj_prj_Y

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
open PI PI.StabSplit PI.StabSplit.Proj
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
variable (H : Matrix n n ℂ) (Y : Matrix n ι ℂ)
namespace PI.StabSplit.Proj
theorem _root_.solution (hG : IsUnit (Yᴴ * H * Y).det) : prj H Y * prj H Y = prj H Y := by
  calc prj H Y * prj H Y = (prj H Y * Y) * (Yᴴ * H * Y)⁻¹ * (Yᴴ * H) := by
        simp only [prj, Matrix.mul_assoc]
    _ = prj H Y := by rw [prj_Y H Y hG]; rfl
end PI.StabSplit.Proj
