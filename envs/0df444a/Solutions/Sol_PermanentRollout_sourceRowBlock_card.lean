-- Prove2me | solution 1 for PermanentRollout.sourceRowBlock_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/1e04a7fd-5063-442b-bedf-7efa00f54ef6

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution (b t : ℕ) (h : Fin b) :
    (sourceRowBlock b t h).card = t := by
  classical
  have hinj : Function.Injective
      (fun j : Fin t =>
        (finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)) (h, j)) := by
    intro left right heq
    exact congrArg Prod.snd
      ((finProdFinEquiv : Fin b × Fin t ≃ Fin (b * t)).injective heq)
  unfold sourceRowBlock
  rw [Finset.card_image_of_injective _ hinj]
  exact Fintype.card_fin t
end PermanentRollout
