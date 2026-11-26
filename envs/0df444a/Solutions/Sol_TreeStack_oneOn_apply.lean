-- Prove2me | solution 1 for TreeStack.oneOn_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:07.275135+00:00
-- url     : https://prove2.me/submissions/1ae67f5d-0d08-4469-8c8f-8ffcde96094b

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {V : Type*} [DecidableEq V] (s : Finset V) (v : V) :
    oneOn s v = if v ∈ s then 1 else 0 := rfl
end TreeStack
