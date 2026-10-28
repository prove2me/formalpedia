-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph_d8e86b30_fed1_4ee5_9c6d_8ff76555c4e7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:01:18.772319+00:00
-- url     : https://prove2.me/submissions/c414738a-dd02-4bd2-b9de-1b45d4c4a18c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_completion_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 ≤ Fintype.card V)
    (hRmax : ∀ S : SimpleGraph V, R ≤ S →
      WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    3 * Fintype.card V = R.edgeSet.ncard + 6 := by
  classical
  obtain ⟨S, hRS, hSdraw, hScard⟩ :=
    WilliamsonShmoys.planar_edge_count_completion_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025
      R hRdraw hCard
  have hSR : S = R := hRmax S hRS hSdraw
  rw [← hSR]
  exact hScard