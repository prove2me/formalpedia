-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_2101673b_57bc_4880_b328_955a83448419_a3__p2m_2101673b_57bc_4880_b328_955a83448419_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T11:49:47.446468+00:00
-- url     : https://prove2.me/submissions/64140126-dd20-4869-80b7-9c0509c871fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_completion__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1

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
    H.Connected ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hconn := WilliamsonShmoys.maximal_planar_graph_connected__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1
    H hH hV hmax
  obtain ⟨K, hK, hsub, hcount⟩ :=
    WilliamsonShmoys.planar_graph_edge_count_completion__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1
      H hH hV
  have hEq : K.edgeSet = H.edgeSet := hmax K hK hsub
  exact ⟨hconn, by simpa [hEq] using hcount⟩