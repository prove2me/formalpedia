-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_419df074_7ffa_4f7d_9922_608f3a25f504_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:48.516535+00:00
-- url     : https://prove2.me/submissions/f9ad5303-25d4-453a-bd26-bfe9c624d3ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_18203136_f8d0_4c28_bbe0_f08319907a9f_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V - 6 = H.edgeSet.ncard := by
  obtain ⟨K, hHK, hKDraw, hKCount⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_18203136_f8d0_4c28_bbe0_f08319907a9f_a1 H hDraw hV
  have hKH : K ≤ H := hmax K hHK hKDraw
  have hEq : K = H := le_antisymm hKH hHK
  rw [← hEq]
  exact hKCount.symm