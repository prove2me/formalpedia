-- Prove2me | solution 1 for PI.StabSplit.Proj.L_prj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:11.913201+00:00
-- url     : https://prove2.me/submissions/ea05c86e-e70e-4f58-818d-8442805cfcba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL

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
theorem _root_.solution (hG : IsUnit (Yᴴ * H * Y).det) : (Yᴴ * H) * prj H Y = Yᴴ * H := by
  calc (Yᴴ * H) * prj H Y = ((Yᴴ * H * Y) * (Yᴴ * H * Y)⁻¹) * (Yᴴ * H) := by
        simp only [prj, Matrix.mul_assoc]
    _ = Yᴴ * H := by rw [mul_nonsing_inv _ hG, Matrix.one_mul]
end PI.StabSplit.Proj
