-- Prove2me | solution 1 for PI.StabSplit.Proj.Y_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:16.772418+00:00
-- url     : https://prove2.me/submissions/1c0d3445-c8a9-4fd5-8262-63f053da04e2

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
theorem _root_.solution (hG : IsUnit (Yᴴ * H * Y).det) (c : ι → ℂ) (hc : Y *ᵥ c = 0) : c = 0 := by
  have h1 : (Yᴴ * H * Y) *ᵥ c = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  have h2 := congrArg (fun v => (Yᴴ * H * Y)⁻¹ *ᵥ v) h1
  simpa [Matrix.mulVec_mulVec, nonsing_inv_mul _ hG] using h2
end PI.StabSplit.Proj
