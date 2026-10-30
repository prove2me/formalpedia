-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_edge_count__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:09:08.378323+00:00
-- url     : https://prove2.me/submissions/ebb8d5c6-0101-4a6c-bf0e-122b977e7370
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V, LE.le K L → WilliamsonShmoys.HasPlanarDrawingOn L → LE.le L K)
    (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys_planar_edge_count_upper_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1 K hKplanar hV
  have hlower := WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1 K hKplanar hKmax hV
  omega