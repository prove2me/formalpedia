-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_has_exact_edge_count__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:17.072645+00:00
-- url     : https://prove2.me/submissions/851be738-2925-4060-9969-2a1240cec28e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion__p2m_60b38c6b_3179_48fe_bb14_f21b6e8b7c6f_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLplanar, hLcount⟩ :=
    WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_60b38c6b_3179_48fe_bb14_f21b6e8b7c6f_a1
      K hplanar hV
  have hLK : L = K := hmax L hKL hLplanar
  simpa [hLK] using hLcount