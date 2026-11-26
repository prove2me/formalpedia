-- Prove2me | solution 1 for TreeStack.mem_support_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:34.37154+00:00
-- url     : https://prove2.me/submissions/a3c266c6-482d-412c-9d79-769133d5e4fc

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_TreeStack_Basic

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {V : Type*} {C : Configuration V} {v : V} :
    v ∈ support C ↔ 0 < C v := Iff.rfl
end TreeStack
