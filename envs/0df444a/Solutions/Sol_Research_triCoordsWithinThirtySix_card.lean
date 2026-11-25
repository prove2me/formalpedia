-- Prove2me | solution 1 for Research.triCoordsWithinThirtySix_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:47:58.098114+00:00
-- url     : https://prove2.me/submissions/5e94b06e-c015-4435-9ae8-83a4f9270b9b

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution :
    triCoordsWithinThirtySix.card = 126 := by
  decide
end Research
