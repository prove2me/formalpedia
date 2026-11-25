-- Prove2me | solution 1 for PI.LocCartanPair.hypJ_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:59.319623+00:00
-- url     : https://prove2.me/submissions/82b30fc5-5b05-4794-91e6-d6fdfd6547a3

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag

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
theorem _root_.solution : (hypJ κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R) * hypJ κ = 1 := by
  simp [hypJ, fromBlocks_multiply]
end PI.LocCartanPair
