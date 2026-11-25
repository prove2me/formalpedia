-- Prove2me | solution 1 for Research.triCoordsWithin_nine_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:13:28.107715+00:00
-- url     : https://prove2.me/submissions/9a90b34b-d2d6-476f-a58d-15250e53905e

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells

set_option autoImplicit true
@[expose] public section
public section
open Research
namespace Research
theorem _root_.solution : (triCoordsWithin 9).card = 36 := by
  decide
end Research
