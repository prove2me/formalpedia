-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_1095f796_c580_4096_843f_cd051f083539_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:50:31.062261+00:00
-- url     : https://prove2.me/submissions/35f32a05-f5df-4a87-b3a7-5bbe033afd39

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_6a98dd8c_93db_41f3_b936_6f734f02a42e_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨T, hKT, hT, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_6a98dd8c_93db_41f3_b936_6f734f02a42e_a1
      K hV hK
  have hTK : T ≤ K := hMax T hKT hT
  have hGraphs : T = K := le_antisymm hTK hKT
  rw [← hGraphs, hCount]