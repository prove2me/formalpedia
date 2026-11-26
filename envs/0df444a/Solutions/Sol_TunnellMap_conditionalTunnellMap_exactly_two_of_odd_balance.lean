-- Prove2me | solution 1 for TunnellMap.conditionalTunnellMap_exactly_two_of_odd_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:23:06.844383+00:00
-- url     : https://prove2.me/submissions/1f51b56d-06ea-441e-a97f-f7f2f9bc7a6e

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_Assembly
import Definitions.Def_TunnellMap_OrbitLift
import Theorems.Thm_TunnellMap_conditionalTunnellMap_exactly_two


set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ}
    (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BOddRep n) = Fintype.card (ARep n))
    (a : ARep n) :
    ∃ x₁ x₂,
      x₁ ≠ x₂ ∧
      conditionalTunnellMap (oddEquivOfBalance hn hnpos hbalance) x₁ = a ∧
      conditionalTunnellMap (oddEquivOfBalance hn hnpos hbalance) x₂ = a ∧
      ∀ x, conditionalTunnellMap (oddEquivOfBalance hn hnpos hbalance) x = a ↔
        x = x₁ ∨ x = x₂ :=
  conditionalTunnellMap_exactly_two (oddEquivOfBalance hn hnpos hbalance) a
end TunnellMap
