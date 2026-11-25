-- Prove2me | solution 1 for P2M_Formalism_LogVandermondeBounds_StandardLattice_not_natAdd_lt_castAdd__c751723af974
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:59.311418+00:00
-- url     : https://prove2.me/submissions/43b43131-ef4a-4ffc-aaac-1ef693835138

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
theorem _root_.solution {a m : ℕ} (i : Fin m) (j : Fin a) :
    ¬ Fin.natAdd a i < Fin.castAdd m j := by
  have := j.2
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd]
  omega
end Formalism.LogVandermondeBounds.StandardLattice
