-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_fd50f30a_a705_4e8f_aa70_6c141aacfb17_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:04:53.069137+00:00
-- url     : https://prove2.me/submissions/aff24756-b09f-4677-9f8e-d76918925deb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count_extension__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a1__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdraw : HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      (forall u v, M.Adj u v -> N.Adj u v) ->
      HasPlanarDrawingOn N ->
      forall u v, N.Adj u v -> M.Adj u v) :
    letI : forall G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 = M.edgeFinset.card := by
  classical
  letI : forall G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  obtain ⟨N, hMN, hNdraw, hNcard⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_extension__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a1__p2m_fc02047b_ad3c_4a9e_81a3_7d77431738b5_a2
      M hcard hdraw
  have hNM : forall u v, N.Adj u v -> M.Adj u v := hmax N hMN hNdraw
  have hEq : M = N := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    exact ⟨hMN u v, hNM u v⟩
  rw [hEq]
  exact hNcard