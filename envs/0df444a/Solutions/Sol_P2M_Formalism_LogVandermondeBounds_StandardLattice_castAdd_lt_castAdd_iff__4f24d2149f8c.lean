-- Prove2me | solution 1 for P2M_Formalism_LogVandermondeBounds_StandardLattice_castAdd_lt_castAdd_iff__4f24d2149f8c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:56.203869+00:00
-- url     : https://prove2.me/submissions/44f42dde-f62b-4f9a-88da-36158c3fae01

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
theorem _root_.solution {a m : ℕ} (i j : Fin a) :
    Fin.castAdd m i < Fin.castAdd m j ↔ i < j := by
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd]
end Formalism.LogVandermondeBounds.StandardLattice
