-- Prove2me | solution 1 for TunnellMap.bLowerK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:36.726982+00:00
-- url     : https://prove2.me/submissions/3579082a-0cc5-44a6-8dff-d4c486829ad6

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
import Theorems.Thm_TunnellMap_ceil_intCast_div_intCast
import Theorems.Thm_TunnellMap_isqrtK_eq
attribute [local simp] TunnellMap.isqrtK_eq



set_option autoImplicit true
open TunnellMap
open OrderedGenerator
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : 0 ≤ n) {p : Triple} (F : OrthogonalFrame p)
    (A q : ℤ) : bLowerK n F A q = bLower n F A q := by
  rw [bLowerK, bLower, ceil_intCast_div_intCast _ _ hn, isqrtK_eq]
end TunnellMap
