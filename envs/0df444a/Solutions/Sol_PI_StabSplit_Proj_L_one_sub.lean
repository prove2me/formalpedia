-- Prove2me | solution 1 for PI.StabSplit.Proj.L_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:40.588802+00:00
-- url     : https://prove2.me/submissions/31a12dee-7d99-45a9-bfd2-da26a91faed4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_PrjMulVecOfL
import Theorems.Thm_PI_StabSplit_Proj_L_prj

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
theorem _root_.solution (hG : IsUnit (Yᴴ * H * Y).det) : (Yᴴ * H) * (1 - prj H Y) = 0 := by
  rw [Matrix.mul_sub, L_prj H Y hG, Matrix.mul_one, sub_self]
end PI.StabSplit.Proj
