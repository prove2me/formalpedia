-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a7
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:54:37.440803+00:00
-- url     : https://prove2.me/submissions/c120e291-230c-4441-af0c-de21bdd86920

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_337d3ec9_bc9c_4a02_9472_77e31d84e6a7_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_337d3ec9_bc9c_4a02_9472_77e31d84e6a7_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      (∀ x y, T.Adj x y → U.Adj x y) ∧
      HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hTU, hU, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_337d3ec9_bc9c_4a02_9472_77e31d84e6a7_a1 T hT
  exact ⟨U, hTU, hU,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_337d3ec9_bc9c_4a02_9472_77e31d84e6a7_a1 U hCard hU hmax⟩