-- Prove2me | solution 1 for TunnellMap.Examples41.isParkingFunction_of_sortedCounts_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:21:18.576056+00:00
-- url     : https://prove2.me/submissions/a1f42abe-7940-4fa7-8709-a9409b2b75db

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution {a b : List ℕ}
    (hpos : ∀ x ∈ a, 0 < x) (hb : sortedCounts a = b)
    (hbound : ∀ i : Fin b.length, b.get i ≤ i.1 + 1) :
    IsParkingFunction a := by
  refine ⟨hpos, ?_⟩
  subst hb
  exact hbound
end TunnellMap.Examples41
