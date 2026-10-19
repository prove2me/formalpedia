-- Prove2me | solution 1 for PermanentRollout.sourceRowBlock_exceptional_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/2323d182-b741-4778-a995-6671b857bb5e

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {b t : ℕ} (omitted : Finset (Fin (b * t)))
    (hnonempty : omitted.Nonempty) {left right : Fin b}
    (hleft : omitted ⊆ sourceRowBlock b t left)
    (hright : omitted ⊆ sourceRowBlock b t right) :
    left = right := by
  by_contra hne
  obtain ⟨row, hrow⟩ := hnonempty
  exact (Finset.disjoint_left.mp (sourceRowBlock_disjoint hne))
    (hleft hrow) (hright hrow)
end PermanentRollout
