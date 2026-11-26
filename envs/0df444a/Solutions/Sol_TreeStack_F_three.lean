-- Prove2me | solution 1 for TreeStack.F_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:54.207928+00:00
-- url     : https://prove2.me/submissions/c785ac7b-ad47-4f8d-97f7-3dbc36930d47

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution : F 3 = 0 := by
  norm_num [F]
end TreeStack
