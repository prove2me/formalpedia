-- Prove2me | solution 1 for TunnellMap.Examples41.generated_row_affine_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:40:42.893091+00:00
-- url     : https://prove2.me/submissions/f7c066d2-9189-49c9-8a27-f36ca4a515d7

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    (rowIndex1.A, rowIndex1.q, rowIndex1.u, rowIndex1.b) = (5, 1, 2, -1) ∧
      (rowIndex2.A, rowIndex2.q, rowIndex2.u, rowIndex2.b) = (5, -1, 2, 1) ∧
      (rowIndex3.A, rowIndex3.q, rowIndex3.u, rowIndex3.b) = (20, 1, 2, -4) ∧
      (rowIndex4.A, rowIndex4.q, rowIndex4.u, rowIndex4.b) = (20, -1, 2, 4) := by
  norm_num [rowIndex1, rowIndex2, rowIndex3, rowIndex4, latticeIndex]
end TunnellMap.Examples41
