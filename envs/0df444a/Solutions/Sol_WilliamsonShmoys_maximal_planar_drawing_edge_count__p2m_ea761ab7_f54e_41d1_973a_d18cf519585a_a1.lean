-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_ea761ab7_f54e_41d1_973a_d18cf519585a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T13:05:24.895946+00:00
-- url     : https://prove2.me/submissions/8557004f-8df9-4843-99da-978f788b025a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_8be6e20d_20e4_4a9a_97eb_8181cc85f42c_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hmax : ∀ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hKM, hM, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_8be6e20d_20e4_4a9a_97eb_8181cc85f42c_a2
      K hK hV
  have hMK : M.edgeSet ⊆ K.edgeSet := hmax M hKM hM
  have hEq : K.edgeSet = M.edgeSet := Set.Subset.antisymm hKM hMK
  simpa [hEq] using hcount