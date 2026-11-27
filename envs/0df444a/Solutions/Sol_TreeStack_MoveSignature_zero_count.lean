-- Prove2me | solution 1 for TreeStack.MoveSignature.zero_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:38.095333+00:00
-- url     : https://prove2.me/submissions/7a6c462e-8572-427c-88c0-f4bb5a8b64cd

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.MoveSignature
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.MoveSignature
theorem _root_.solution (u v : V) :
    (zero T).count u v = 0 := rfl
end TreeStack.MoveSignature
