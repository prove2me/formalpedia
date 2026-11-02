-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound__p2m_267a842e_101e_4cf6_b705_d11d92433d33_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:38:15.528949+00:00
-- url     : https://prove2.me/submissions/cca377fe-1e53-451b-b805-c45946f6bce0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_supergraph_edge_count__p2m_33702fa3_4ca0_4ee2_9d3c_676a8b8ff565_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K -> LE.le H K -> K = H) :
    (letI : DecidableRel H.Adj := dH;
     3 * Fintype.card V - 6 <= H.edgeFinset.card) := by
  letI : DecidableRel H.Adj := dH
  obtain ⟨K, dK, hK, hHK, hcount⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulated_supergraph_edge_count__p2m_33702fa3_4ca0_4ee2_9d3c_676a8b8ff565_a1 H hH hn
  have hEq : K = H := hmax K hK hHK
  subst K
  have hd : dK = dH := by
    funext u v
    exact Subsingleton.elim _ _
  subst dK
  omega