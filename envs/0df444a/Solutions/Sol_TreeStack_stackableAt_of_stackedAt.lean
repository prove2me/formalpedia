-- Prove2me | solution 1 for TreeStack.stackableAt_of_stackedAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:26.240063+00:00
-- url     : https://prove2.me/submissions/7d7ce3b0-79f2-4534-a2f7-d3b07c855ed0

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (C : Configuration V) (r : V) (h : StackedAt C r) :
    StackableAt G C r :=
  ⟨C, Relation.ReflTransGen.refl, h⟩
end TreeStack
