-- Prove2me | solution 1 for PI.StabSplit.Proj.prj_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:47.233572+00:00
-- url     : https://prove2.me/submissions/6c1f506e-ca64-4154-9ee9-ef93477c0336

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
theorem _root_.solution (hH : Hᴴ = H) : (prj H Y)ᴴ * H = H * prj H Y := by
  simp only [prj, conjTranspose_mul, conjTranspose_nonsing_inv, hH, conjTranspose_conjTranspose,
    Matrix.mul_assoc]
end PI.StabSplit.Proj
