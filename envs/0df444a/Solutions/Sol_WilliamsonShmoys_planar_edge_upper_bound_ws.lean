-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_ws
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:58:47.701579+00:00
-- url     : https://prove2.me/submissions/38223b87-5a66-464d-a48a-0e81dad4b252
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_ws
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ws
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_ws

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) : M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hMH, hH, hmaxM⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_ws M hM hcard
  have hmaxH : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by
    intro K hHK hK
    exact hmaxM K (le_trans hMH hHK) hK
  have hcount := WilliamsonShmoys.maximal_planar_edge_count_ws H hH hcard hmaxH
  have hmono := WilliamsonShmoys.edgeSet_ncard_mono_ws M H hMH
  omega