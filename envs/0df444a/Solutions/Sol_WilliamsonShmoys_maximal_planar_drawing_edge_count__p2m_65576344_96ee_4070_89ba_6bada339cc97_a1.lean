-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_65576344_96ee_4070_89ba_6bada339cc97_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:05:42.019953+00:00
-- url     : https://prove2.me/submissions/1f0b8f83-a8f3-42b9-a285-5f6e4df1f066
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_03e1b202_06dc_4da5_bd81_d67a28c40fa1_a1
import Theorems.Thm_WilliamsonShmoys_planar_triangulated_supergraph__p2m_03e1b202_06dc_4da5_bd81_d67a28c40fa1_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hKcount⟩ :=
    WilliamsonShmoys.planar_triangulated_supergraph__p2m_03e1b202_06dc_4da5_bd81_d67a28c40fa1_a1
      H hH hV
  have hKH : K.edgeSet.ncard ≤ H.edgeSet.ncard := hMax K hHK hK
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_03e1b202_06dc_4da5_bd81_d67a28c40fa1_a1
      H hH hV
  omega