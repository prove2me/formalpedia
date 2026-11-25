-- Prove2me | solution 1 for Research.shellSixOffsets_boundary_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:22:55.041253+00:00
-- url     : https://prove2.me/submissions/d305546d-58a8-4fbf-93b5-672f3c8a0c33

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
    (∑ d ∈ shellSixOffsets, (d.1.natAbs + d.2.natAbs)) = 732 ∧
    (∑ d ∈ shellSixOffsets, d.1.natAbs * d.2.natAbs) = 998 := by
  decide
end Research
