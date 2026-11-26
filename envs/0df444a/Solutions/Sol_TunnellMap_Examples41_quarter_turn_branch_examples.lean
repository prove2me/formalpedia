-- Prove2me | solution 1 for TunnellMap.Examples41.quarter_turn_branch_examples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:38:17.849795+00:00
-- url     : https://prove2.me/submissions/09027fd2-852e-49df-be4c-2d9df107bf6b

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    (branch1Equiv 11 branch1Source11).rep.1 = ⟨1, -3, 0⟩ ∧
      (branch2Equiv 11 branch2Source11).rep.1 = ⟨1, 3, 0⟩ ∧
      (branch3Equiv 41 branch3Source41).rep.1 = ⟨2, -1, 1⟩ ∧
      (branch3Equiv 41).symm (branch3Equiv 41 branch3Source41) = branch3Source41 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · exact (branch3Equiv 41).left_inv branch3Source41
end TunnellMap.Examples41
