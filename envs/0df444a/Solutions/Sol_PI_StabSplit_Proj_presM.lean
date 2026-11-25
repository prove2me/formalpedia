-- Prove2me | solution 1 for PI.StabSplit.Proj.presM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:11.628798+00:00
-- url     : https://prove2.me/submissions/3575ce23-dd7b-4537-958b-8900c4246807

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
theorem _root_.solution (hG : IsUnit (Yᴴ * H * Y).det) (g : Matrix n n ℂ) (C : Matrix ι ι ℂ) (hC : g * Y = Y * C) :
    (1 - prj H Y) * g * prj H Y = 0 := by
  have : g * prj H Y = Y * C * ((Yᴴ * H * Y)⁻¹ * (Yᴴ * H)) := by
    rw [prj, Matrix.mul_assoc Y, ← Matrix.mul_assoc g, hC]
  rw [Matrix.mul_assoc, this, Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc (prj H Y),
    ← Matrix.mul_assoc (prj H Y), prj_Y H Y hG, sub_self]
end PI.StabSplit.Proj
