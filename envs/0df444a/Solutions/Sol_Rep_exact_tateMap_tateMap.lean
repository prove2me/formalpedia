-- Prove2me | solution 1 for Rep.exact_tateMap_tateMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c43305f6-e2e8-5bc1-816a-3cbb821d8772

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Theorems.Thm_Rep_exact_tateH0Map_tateH0Map
import Theorems.Thm_Rep_exact_tateHneg1Map_tateHneg1Map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exact_tateMap_tateMap

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    Function.Exact (Rep.tateMap X.f n).hom (Rep.tateMap X.g n).hom := by
  match n with
  | Int.ofNat (m + 1) =>
    exact LinearMap.exact_iff.2 (groupCohomology.mapShortComplex₂_exact hX (m + 1)).moduleCat_range_eq_ker.symm
  | Int.ofNat 0 => exact Rep.exact_tateH0Map_tateH0Map hX
  | Int.negSucc 0 => exact Rep.exact_tateHneg1Map_tateHneg1Map hX
  | Int.negSucc (m + 1) =>
    exact LinearMap.exact_iff.2 (groupHomology.mapShortComplex₂_exact hX (m + 1)).moduleCat_range_eq_ker.symm

end S_Rep_exact_tateMap_tateMap
end P2MW
export P2MW.S_Rep_exact_tateMap_tateMap (solution)
