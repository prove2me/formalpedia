-- Prove2me | solution 1 for TunnellMap.bValues_sort_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:24.635647+00:00
-- url     : https://prove2.me/submissions/a4e65d25-65c8-47cd-b967-c015d4eeb0a5

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
import Theorems.Thm_TunnellMap_intIcc_sort_eq
import Theorems.Thm_TunnellMap_bLowerK_eq
import Theorems.Thm_TunnellMap_bUpperK_eq

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : 0 ≤ n) {p : Triple} (F : OrthogonalFrame p)
    (A q : ℤ) : (bValues n F A q).sort (· ≤ ·) = bValuesL n F A q := by
  rw [bValues, intIcc_sort_eq, bValuesL, bLowerK_eq hn, bUpperK_eq hn]
end TunnellMap
