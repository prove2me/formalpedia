-- Prove2me | solution 1 for TunnellMap.bUpperK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:45.903875+00:00
-- url     : https://prove2.me/submissions/1d8e1c8b-32b2-49da-9070-b65acf9fb620

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
import Theorems.Thm_TunnellMap_floor_intCast_div_intCast
import Theorems.Thm_TunnellMap_isqrtK_eq
attribute [local simp] TunnellMap.isqrtK_eq



set_option autoImplicit true
open TunnellMap
open OrderedGenerator
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : 0 ≤ n) {p : Triple} (F : OrthogonalFrame p)
    (A q : ℤ) : bUpperK n F A q = bUpper n F A q := by
  rw [bUpperK, bUpper, floor_intCast_div_intCast _ _ hn, isqrtK_eq]
end TunnellMap
