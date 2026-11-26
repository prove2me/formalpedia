-- Prove2me | solution 1 for TreeStack.stackable_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:05.131285+00:00
-- url     : https://prove2.me/submissions/016b37e1-ec6b-4047-922a-0004f496bde3

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {C D : Configuration V}
    (hCD : PebbleStep G C D) (hD : Stackable G D) : Stackable G C := by
  rcases hD with ⟨r, E, hDE, hE⟩
  exact ⟨r, E, Relation.ReflTransGen.head hCD hDE, hE⟩
end TreeStack
