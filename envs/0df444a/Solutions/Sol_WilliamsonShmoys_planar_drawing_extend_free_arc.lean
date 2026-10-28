-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extend_free_arc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:30:38.176245+00:00
-- url     : https://prove2.me/submissions/13995ece-c220-46fd-b224-717ae1572800
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_IsPlanarDrawingData
import Definitions.Def_WilliamsonShmoys_HasFreeConnectingArc
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_data_extend_free_arc_to_supergraph
import Theorems.Thm_WilliamsonShmoys_exists_supergraph_adding_nonedge

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hDrawing : WilliamsonShmoys.IsPlanarDrawingData G p arc)
    (u v : V) (hNotAdj : ¬ G.Adj u v)
    (hFree : WilliamsonShmoys.HasFreeConnectingArc G p arc u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hSub, hAdj, hOnly⟩ :=
    WilliamsonShmoys.exists_supergraph_adding_nonedge G u v hNotAdj
  exact ⟨H, hSub, hAdj,
    WilliamsonShmoys.planar_drawing_data_extend_free_arc_to_supergraph
      G H p arc u v hDrawing hFree hSub hAdj hOnly⟩