-- Prove2me | solution 1 for Research.shellSixOffsets_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:17:21.988906+00:00
-- url     : https://prove2.me/submissions/a2e83e56-5f83-48a2-b1b9-2986d9ea9771

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
theorem _root_.solution : shellSixOffsets.card = 128 := by
  decide
end Research
