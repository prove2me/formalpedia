-- Prove2me | solution 1 for TunnellMap.Examples41.generated_row_directions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:40:48.175194+00:00
-- url     : https://prove2.me/submissions/8da9752a-8aa1-4470-8342-c677dbf039a4

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    dValue frame41 rowIndex1 = ⟨1, -1, 1⟩ ∧
      dValue frame41 rowIndex2 = ⟨1, 1, 1⟩ ∧
      dValue frame41 rowIndex3 = ⟨1, -4, 1⟩ ∧
      dValue frame41 rowIndex4 = ⟨1, 4, 1⟩ := by
  norm_num [rowIndex1, rowIndex2, rowIndex3, rowIndex4, latticeIndex,
    dValue, rValue, aValue, frame41, alpha, beta, delta, linComb3, vadd,
    vsmul, tauInv, dot]
end TunnellMap.Examples41
