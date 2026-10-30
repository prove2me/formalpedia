-- Prove2me | solution 1 for WilliamsonShmoys.planar_inclusion_maximal_to_triangular_map__p2m_a5aa844d_3de6_493d_889d_66e8736d1b42_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T11:45:41.344789+00:00
-- url     : https://prove2.me/submissions/c42b0d34-261d-478c-8d3f-e91063528d23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_2101673b_57bc_4880_b328_955a83448419_a3__p2m_2101673b_57bc_4880_b328_955a83448419_a4
import Theorems.Thm_WilliamsonShmoys_triangular_map_of_planar_maximal_edge_count__p2m_2101673b_57bc_4880_b328_955a83448419_a3__p2m_2101673b_57bc_4880_b328_955a83448419_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeSet ⊆ K.edgeSet → K.edgeSet = H.edgeSet) :
    ∃ (m : Nat), Nonempty (WilliamsonShmoys.TriangularMap H (Fin m)) := by
  obtain ⟨hconn, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_2101673b_57bc_4880_b328_955a83448419_a3__p2m_2101673b_57bc_4880_b328_955a83448419_a4
      H hH hV hmax
  exact WilliamsonShmoys.triangular_map_of_planar_maximal_edge_count__p2m_2101673b_57bc_4880_b328_955a83448419_a3__p2m_2101673b_57bc_4880_b328_955a83448419_a4
    H hH hV hconn hcount