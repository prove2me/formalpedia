-- Prove2me | solution 1 for Research.shellSixOffsets_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:02:57.134126+00:00
-- url     : https://prove2.me/submissions/e362e8d7-c4c6-410b-8959-f142e7e50b88

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
    ∑ d ∈ shellSixOffsets,
      (365 - d.1.natAbs) * (365 - d.2.natAbs) = 16786618 := by
  decide
end Research
