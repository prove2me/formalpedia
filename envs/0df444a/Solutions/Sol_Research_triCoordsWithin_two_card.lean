-- Prove2me | solution 1 for Research.triCoordsWithin_two_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:58:25.606817+00:00
-- url     : https://prove2.me/submissions/766409af-9460-49f4-84a5-4210a590932a

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells

set_option autoImplicit true
@[expose] public section
public section
open Research
namespace Research
theorem _root_.solution : (triCoordsWithin 2).card = 6 := by
  decide
end Research
