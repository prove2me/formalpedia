-- Prove2me | solution 1 for PI.LocCartanPair.hypJ_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:47.083994+00:00
-- url     : https://prove2.me/submissions/23b475b0-5de7-4dbc-9af5-08fa01d499b6

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag
import Theorems.Thm_PI_LocCartanPair_hypJ_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocCartanPair
open Matrix IsLocalRing
variable {R : Type} [CommRing R] [StarRing R]
variable (κ : Type) [Fintype κ] [DecidableEq κ]
namespace PI.LocCartanPair
theorem _root_.solution : IsUnit (hypJ κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R).det := by
  refine IsUnit.of_mul_eq_one (hypJ κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R).det ?_
  rw [← det_mul, hypJ_sq, det_one]
end PI.LocCartanPair
