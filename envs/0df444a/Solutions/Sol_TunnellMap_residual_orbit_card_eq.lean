-- Prove2me | solution 1 for TunnellMap.residual_orbit_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:23.406499+00:00
-- url     : https://prove2.me/submissions/bead7b14-eaf7-4292-9e26-6d2adf60d5d1

import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_ResidualBalance
import Theorems.Thm_TunnellMap_residual_card_eq
import Theorems.Thm_TunnellMap_FreeInvolution_card_eq_twice_orbit_card


set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n) (hnpos : 0 < n)
    [Fintype (BOddRep n)] [Fintype (ARep n)]
    (hbalance : Fintype.card (BOddRep n) = Fintype.card (ARep n)) :
    Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit := by
  classical
  let BI := bResidualInvolution n
  let AI := aResidualInvolution n hnpos
  letI : Fintype BI.Orbit := BI.orbitFintype
  letI : Fintype AI.Orbit := AI.orbitFintype
  have hres := residual_card_eq hn hbalance
  have hb := BI.card_eq_twice_orbit_card
  have ha := AI.card_eq_twice_orbit_card
  change Fintype.card BI.Orbit = Fintype.card AI.Orbit
  omega
end TunnellMap
