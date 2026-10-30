-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:41:00.989634+00:00
-- url     : https://prove2.me/submissions/48a1ad25-b666-4816-93d1-c56ca876f634

import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_of_downward_closed_graph_property__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph_hereditary__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N := by
  exact WilliamsonShmoys.finite_maximal_extension_of_downward_closed_graph_property__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1
    M HasPlanarDrawingOn
    (fun {G H : SimpleGraph V} (hGH : G ≤ H) (hH : HasPlanarDrawingOn H) =>
      WilliamsonShmoys.planar_drawing_subgraph_hereditary__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1 hGH hH)
    hDraw