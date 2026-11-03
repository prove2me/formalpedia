-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_edge_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:56:27.424949+00:00
-- url     : https://prove2.me/submissions/bc88478a-d676-465e-855c-641745e55967

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_to_planarMapDataExtension__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1
import Theorems.Thm_WilliamsonShmoys_planarMapDataExtension_edge_bound__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 <= Fintype.card V) :
    J.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  classical
  obtain ⟨K, hK, hsub, hdata⟩ :=
    WilliamsonShmoys.planarDrawingOn_to_planarMapDataExtension__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1
      J hJ hcard
  letI : DecidableRel K.Adj := hK
  exact WilliamsonShmoys.planarMapDataExtension_edge_bound__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1
    J K hcard hsub hdata