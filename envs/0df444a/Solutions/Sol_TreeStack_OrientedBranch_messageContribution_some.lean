-- Prove2me | solution 1 for TreeStack.OrientedBranch.messageContribution_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:18:25.147212+00:00
-- url     : https://prove2.me/submissions/3a57bddf-c2e0-4367-8d4e-1194eb616551

import Mathlib
import Definitions.Def_TreeStack_Transfer
import Definitions.Def_TreeStack_Branch
import Definitions.Def_TreeStack_Message

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (d : ℤ) :
    messageContribution (some d) = d := rfl
end TreeStack.OrientedBranch
