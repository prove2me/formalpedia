-- Prove2me | solution 1 for PI.BlockRatReal.detShift_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:39.952246+00:00
-- url     : https://prove2.me/submissions/4c458b0c-9d55-48ee-8246-6dc948334f4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_AntitoneStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal
namespace PI.BlockRatReal
theorem _root_.solution {m : ℕ} (w : Fin (m + 1) → ℤ) : detShift w = w (Fin.last m) := by
  rw [detShift, dif_pos (Nat.succ_pos m)]
  rfl
end PI.BlockRatReal
