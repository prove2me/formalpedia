-- Prove2me | solution 1 for PI.StabSplit.Proj.prj_Y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:41.824774+00:00
-- url     : https://prove2.me/submissions/a0166e32-326a-4d40-8edb-fd3e4c40c87e

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
theorem _root_.solution (hG : IsUnit (Yᴴ * H * Y).det) : prj H Y * Y = Y := by
  calc prj H Y * Y = Y * ((Yᴴ * H * Y)⁻¹ * (Yᴴ * H * Y)) := by simp only [prj, Matrix.mul_assoc]
    _ = Y := by rw [nonsing_inv_mul _ hG, Matrix.mul_one]
end PI.StabSplit.Proj
