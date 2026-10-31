-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:28.279946+00:00
-- url     : https://prove2.me/submissions/f57f88f6-4bd8-406e-9d59-1573cc0991a0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_exact_edge_count__p2m_db7ffdc7_d913_4822_af5b_b88ad4555746_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 = H.edgeSet.ncard := by
  obtain ⟨T, hHT, hT, hCount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_supergraph_exact_edge_count__p2m_db7ffdc7_d913_4822_af5b_b88ad4555746_a1
      H hV hH
  have hEq : T = H := hmax T hHT hT
  rw [← hEq]
  exact hCount