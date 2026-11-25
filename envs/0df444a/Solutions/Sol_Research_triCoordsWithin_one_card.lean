-- Prove2me | solution 1 for Research.triCoordsWithin_one_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:12:20.232815+00:00
-- url     : https://prove2.me/submissions/a3443cc1-6216-4f4f-b941-825db5113c29

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells

set_option autoImplicit true
@[expose] public section
public section
open Research
namespace Research
theorem _root_.solution : (triCoordsWithin 1).card = 6 := by
  decide
end Research
