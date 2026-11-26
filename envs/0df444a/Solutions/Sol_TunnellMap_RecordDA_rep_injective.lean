-- Prove2me | solution 1 for TunnellMap.RecordDA.rep_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:27:05.824093+00:00
-- url     : https://prove2.me/submissions/73b9d918-6306-4c43-ba81-10edd240f663

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution :
    Function.Injective (canonicalBResidualRepresentative (n := n)) := by
  intro q₁ q₂ h
  rw [← orbOf_rep q₁, ← orbOf_rep q₂, h]
end TunnellMap.RecordDA
