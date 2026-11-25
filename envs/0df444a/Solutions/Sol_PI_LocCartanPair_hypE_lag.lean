-- Prove2me | solution 1 for PI.LocCartanPair.hypE_lag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:51:12.633865+00:00
-- url     : https://prove2.me/submissions/54425309-5edf-4c49-b084-4f06cf828eea

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
theorem _root_.solution : (hypE κ : Matrix (κ ⊕ κ) (κ ⊕ κ) R)ᴴ * hypJ κ = hypJ κ * (1 - hypE κ) := by
  have h1 : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) R) - hypE κ = fromBlocks 0 0 0 1 := by
    rw [← fromBlocks_one, hypE, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    simp
  rw [h1]
  simp [hypE, hypJ, fromBlocks_conjTranspose, fromBlocks_multiply]
end PI.LocCartanPair
