-- Prove2me | solution 1 for WilliamsonShmoys.completion_maximal_edge_count_e7f6fb70
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T01:52:19.844766+00:00
-- url     : https://prove2.me/submissions/3bda35c3-99bc-4db3-b088-f65e84bf026a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_max_edges_from_drawing_e7f6fb70__p2m_58175b1d_a153_41c0_9a66_d5e759d3d2be_a5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      (forall {u v}, H.Adj u v -> K.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      forall {u v}, K.Adj u v -> H.Adj u v) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_completion_max_edges_from_drawing_e7f6fb70__p2m_58175b1d_a153_41c0_9a66_d5e759d3d2be_a5 H hV hH
  have hKH : forall {u v}, K.Adj u v -> H.Adj u v :=
    hmax K hHK hKplanar
  have hEq : H = K := by
    ext u v
    constructor
    · exact hHK (u := u) (v := v)
    · exact hKH (u := u) (v := v)
  rw [hEq]
  exact hKcount