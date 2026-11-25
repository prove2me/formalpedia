-- Prove2me | solution 1 for PI.StabSplit.Proj.prj_mul_of_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:32:52.288701+00:00
-- url     : https://prove2.me/submissions/0b6a5e3e-d6ce-4162-92dd-2febc16d8182

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
theorem _root_.solution {m : Type*} [Fintype m] (A : Matrix n m ℂ) (hA : (Yᴴ * H) * A = 0) :
    prj H Y * A = 0 := by
  rw [prj, Matrix.mul_assoc, hA, Matrix.mul_zero]
end PI.StabSplit.Proj
