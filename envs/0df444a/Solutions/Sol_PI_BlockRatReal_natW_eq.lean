-- Prove2me | solution 1 for PI.BlockRatReal.natW_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:10.866244+00:00
-- url     : https://prove2.me/submissions/8471874d-bcb2-41ce-a0b6-63b0a9b5d51d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_AntitoneStar
import Theorems.Thm_PI_BlockRatReal_detShift_eq

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
theorem _root_.solution {m : ℕ} (w : Fin (m + 1) → ℤ) : natW w = nuOf w := by
  funext i
  rw [natW, nuOf, detShift_eq]
end PI.BlockRatReal
