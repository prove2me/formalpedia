-- Prove2me | solution 1 for Research.triCoordsWithin_three_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:12:22.830586+00:00
-- url     : https://prove2.me/submissions/19cfdf9c-f38f-46ac-b96a-d997fe82bfd8

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells

set_option autoImplicit true
@[expose] public section
public section
open Research
namespace Research
theorem _root_.solution : (triCoordsWithin 3).card = 12 := by
  decide
end Research
