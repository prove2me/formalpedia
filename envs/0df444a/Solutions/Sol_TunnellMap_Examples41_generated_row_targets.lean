-- Prove2me | solution 1 for TunnellMap.Examples41.generated_row_targets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:41:08.769209+00:00
-- url     : https://prove2.me/submissions/af0d3d23-fe90-4062-b678-102345f5cba4

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    targetValue s2 frame41 rowIndex1 = ⟨4, 3, 0⟩ ∧
      targetValue s2 frame41 rowIndex2 = ⟨0, 3, -4⟩ ∧
      targetValue s2 frame41 rowIndex3 = ⟨4, -3, 0⟩ ∧
      targetValue s2 frame41 rowIndex4 = ⟨0, -3, -4⟩ := by
  norm_num [rowIndex1, rowIndex2, rowIndex3, rowIndex4, latticeIndex,
    targetValue, dValue, rValue, aValue, frame41, alpha, beta, delta,
    linComb3, vadd, vsmul, tauInv, s2, midpointSource, residualSourceLift,
    bLift, negTriple, dot, reconstructedTarget]
end TunnellMap.Examples41
