-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:00:16.426592+00:00
-- url     : https://prove2.me/submissions/34c49189-1b16-4ba8-892b-7d82f45f323a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound__p2m_85ec4d12_af4e_4e6b_adb3_c8b105f3133d_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ {u v : V}, H.Adj u v -> K.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeFinset.card := by
  classical
  obtain ⟨K, hHK, hK, hKbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_85ec4d12_af4e_4e6b_adb3_c8b105f3133d_a1
      H hH hcard
  have hEq : K = H := hmax K (by
    intro u v huv
    exact hHK huv) hK
  subst K
  exact hKbound