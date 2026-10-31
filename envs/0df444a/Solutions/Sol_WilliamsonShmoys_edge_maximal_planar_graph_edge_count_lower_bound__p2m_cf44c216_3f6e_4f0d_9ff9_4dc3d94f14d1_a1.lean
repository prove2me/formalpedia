-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_edge_count_lower_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T11:00:08.16076+00:00
-- url     : https://prove2.me/submissions/123e62c7-07b0-4aa6-b4ae-8cc063229cc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_exact_maximal_edge_count__p2m_b086cf8e_feab_4218_a571_b7d2828fd0cf_a1
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      (forall {u v : V}, K.Adj u v -> L.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  obtain ⟨L, hsub, hdraw, hcount⟩ :=
    WilliamsonShmoys.planar_supergraph_with_exact_maximal_edge_count__p2m_b086cf8e_feab_4218_a571_b7d2828fd0cf_a1
      K hV hK
  have hLK : L = K := hmax L hsub hdraw
  rw [hLK] at hcount
  omega
