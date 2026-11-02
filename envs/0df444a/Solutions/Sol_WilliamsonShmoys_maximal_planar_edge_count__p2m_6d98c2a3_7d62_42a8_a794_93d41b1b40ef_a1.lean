-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:46:14.423191+00:00
-- url     : https://prove2.me/submissions/5c7db8fa-8157-40c7-bf8c-35c1d4de76f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_3ea6bb1c_a422_4d1c_b17f_ef9a0e48b692_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_3ea6bb1c_a422_4d1c_b17f_ef9a0e48b692_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K)
    (hV : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    letI : Fintype ↑K.edgeSet := Fintype.ofFinite _
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.planar_edge_upper_bound__p2m_3ea6bb1c_a422_4d1c_b17f_ef9a0e48b692_a1 K hK hV
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_3ea6bb1c_a422_4d1c_b17f_ef9a0e48b692_a1 K hK hmax hV
  omega