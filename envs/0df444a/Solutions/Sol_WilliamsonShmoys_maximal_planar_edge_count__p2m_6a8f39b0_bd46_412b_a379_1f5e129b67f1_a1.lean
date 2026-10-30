-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6a8f39b0_bd46_412b_a379_1f5e129b67f1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:23:53.135614+00:00
-- url     : https://prove2.me/submissions/c2d3ba8c-31aa-4a39-a849-9b646f07b5b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_drawing__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1
import Theorems.Thm_WilliamsonShmoys_drawable_edge_lower_bound_extension__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_bound_of_drawing__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1
      K hK hV
  obtain ⟨L, hKL, hL, hLower⟩ :=
    WilliamsonShmoys.drawable_edge_lower_bound_extension__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1
      K hK hV
  have hLK : L ≤ K := hmax L hKL hL
  have hEq : K = L := le_antisymm hKL hLK
  rw [← hEq] at hLower
  omega