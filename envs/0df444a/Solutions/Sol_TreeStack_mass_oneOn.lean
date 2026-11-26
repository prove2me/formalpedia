-- Prove2me | solution 1 for TreeStack.mass_oneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:24.028022+00:00
-- url     : https://prove2.me/submissions/3ddbed65-71f5-46d9-be11-2ea6c35cece1

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
import Theorems.Thm_TreeStack_oneOn_apply
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.oneOn_apply

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (s : Finset V) :
    mass (oneOn s) = s.card := by
  classical
  simp [mass, oneOn]
end TreeStack
