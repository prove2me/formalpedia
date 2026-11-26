-- Prove2me | solution 1 for TunnellMap.BlockGen.blockIndexListK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:43.550845+00:00
-- url     : https://prove2.me/submissions/e9d4e16b-c24c-4dcf-9842-66b197e3991e

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
import Theorems.Thm_TunnellMap_qValues_sort_eq
import Theorems.Thm_TunnellMap_bValues_sort_eq
import Theorems.Thm_TunnellMap_rootValues_sort_eq

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
open TunnellMap.BlockGen
variable {n : ℤ} {p : Triple}
namespace TunnellMap.BlockGen
theorem _root_.solution (hn : 0 ≤ n) (F : OrthogonalFrame p) (h : ℤ) :
    blockIndexListK n F h = blockIndexList n F h := by
  rw [blockIndexListK, blockIndexList, qValues_sort_eq]
  refine List.flatMap_congr fun q _ => ?_
  rw [bValues_sort_eq hn]
  refine List.flatMap_congr fun b _ => ?_
  rw [rootValues_sort_eq]
end TunnellMap.BlockGen
