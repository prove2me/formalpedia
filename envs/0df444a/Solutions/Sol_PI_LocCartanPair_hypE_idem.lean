-- Prove2me | solution 1 for PI.LocCartanPair.hypE_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:51:06.036296+00:00
-- url     : https://prove2.me/submissions/dd594d57-e5f3-4f42-b55e-d15ff7f1d3e9

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
theorem _root_.solution : (hypE κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R) * hypE κ = hypE κ := by
  simp [hypE, fromBlocks_multiply]
end PI.LocCartanPair
