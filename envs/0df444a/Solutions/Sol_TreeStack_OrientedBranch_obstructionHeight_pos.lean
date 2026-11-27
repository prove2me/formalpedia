-- Prove2me | solution 1 for TreeStack.OrientedBranch.obstructionHeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:54:57.198088+00:00
-- url     : https://prove2.me/submissions/4df1b1bd-9c56-42ed-b89e-4d7c8c05b65b

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
open TreeStack.OrientedBranch
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) :
    0 < obstructionHeight B := by
  rw [obstructionHeight]
  split_ifs <;> positivity
end TreeStack.OrientedBranch
