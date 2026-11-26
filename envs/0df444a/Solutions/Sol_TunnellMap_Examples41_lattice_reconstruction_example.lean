-- Prove2me | solution 1 for TunnellMap.Examples41.lattice_reconstruction_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:40:26.214714+00:00
-- url     : https://prove2.me/submissions/4ca33a6a-be4b-4844-8120-da44dc44ba64

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    aValue frame41 latticeIndex = 2 ∧
      rValue frame41 latticeIndex = ⟨2, -4, 0⟩ ∧
      dValue frame41 latticeIndex = ⟨1, -4, 1⟩ ∧
      targetValue s2 frame41 latticeIndex = ⟨4, -3, 0⟩ := by
  norm_num [latticeIndex, aValue, rValue, dValue, targetValue, frame41,
    alpha, beta, delta, linComb3, vadd, vsmul, tauInv, s2, midpointSource,
    residualSourceLift, bLift, negTriple, dot, reconstructedTarget]
end TunnellMap.Examples41
