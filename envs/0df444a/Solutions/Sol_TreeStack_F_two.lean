-- Prove2me | solution 1 for TreeStack.F_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:47.983006+00:00
-- url     : https://prove2.me/submissions/90e84e4b-d888-4275-95a2-d1a253bb9e1a

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution : F 2 = 1 := by
  norm_num [F]
end TreeStack
