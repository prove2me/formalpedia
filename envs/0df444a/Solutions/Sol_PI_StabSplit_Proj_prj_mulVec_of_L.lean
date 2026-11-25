-- Prove2me | solution 1 for PI.StabSplit.Proj.prj_mulVec_of_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:17.049966+00:00
-- url     : https://prove2.me/submissions/92eacf8f-bf65-46d5-95fe-96b01b603350

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
theorem _root_.solution {v : n → ℂ} (hv : (Yᴴ * H) *ᵥ v = 0) : prj H Y *ᵥ v = 0 := by
  rw [prj, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
end PI.StabSplit.Proj
