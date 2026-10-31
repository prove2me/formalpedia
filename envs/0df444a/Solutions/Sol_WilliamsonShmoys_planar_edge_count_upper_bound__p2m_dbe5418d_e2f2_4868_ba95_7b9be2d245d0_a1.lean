-- Prove2me | solution 1 for WilliamsonShmoys_planar_edge_count_upper_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:13:01.012462+00:00
-- url     : https://prove2.me/submissions/dfd49414-a0c0-4239-843e-e988343367f1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKplanar : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hHplanar, hHmax⟩ := WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1 K hKplanar hV
  have hHcount := WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_808b4142_3aa4_463f_be5d_a7d43b832047_a1 H hHplanar hV hHmax
  calc
    K.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono (SimpleGraph.edgeSet_mono hKH)
    _ = 3 * Fintype.card V - 6 := hHcount