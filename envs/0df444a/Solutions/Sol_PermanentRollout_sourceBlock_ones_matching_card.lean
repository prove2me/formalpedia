-- Prove2me | solution 1 for PermanentRollout.sourceBlock_ones_matching_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/e8da1b72-a8ca-4f97-abfe-39d12b7ac7f8

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace PermanentRollout
theorem _root_.solution
    (s d : ℕ) (J : Finset (Fin s)) (hJ : J.card = d) :
    Fintype.card
      (Fin (s - d) ≃ {column : Fin s // column ∉ J}) =
      (s - d).factorial := by
  simpa using Fintype.card_equiv (sourceBlockOnesEquiv s d J hJ)
end PermanentRollout
