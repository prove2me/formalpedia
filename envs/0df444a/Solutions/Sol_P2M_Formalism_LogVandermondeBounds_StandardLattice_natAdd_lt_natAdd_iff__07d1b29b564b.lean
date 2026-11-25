-- Prove2me | solution 1 for P2M_Formalism_LogVandermondeBounds_StandardLattice_natAdd_lt_natAdd_iff__07d1b29b564b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:58.326331+00:00
-- url     : https://prove2.me/submissions/c1cea2ea-720a-42a3-a11c-5b65c6dcee87

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution {a m : ℕ} (i j : Fin m) :
    Fin.natAdd a i < Fin.natAdd a j ↔ i < j := by
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_natAdd]
  omega
end Formalism.LogVandermondeBounds.StandardLattice
