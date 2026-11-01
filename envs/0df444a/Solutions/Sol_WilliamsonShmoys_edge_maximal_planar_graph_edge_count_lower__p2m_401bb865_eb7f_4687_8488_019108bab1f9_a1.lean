-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_edge_count_lower__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:41:31.610168+00:00
-- url     : https://prove2.me/submissions/f207a84a-72a2-43fd-bf3d-c98600415b46
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph__p2m_2d4d5aa9_1174_4f98_adfa_d1e94ce87256_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ->
      (forall u v, N.Adj u v -> P.Adj u v) -> P = N) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 := by
  obtain ⟨P, hP, hsub, hcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_2d4d5aa9_1174_4f98_adfa_d1e94ce87256_a1
      N hN hcard
  have hPN : P = N := hmax P hP hsub
  subst P
  omega