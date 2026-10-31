-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_45b06a26_f6d7_4266_b401_312835dd7478_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:29.56526+00:00
-- url     : https://prove2.me/submissions/476cc016-2b07-4ada-bb8c-f47e7a790919

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph__p2m_8c6de935_4f5b_49ef_8949_a6af2a37957f_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hCount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_8c6de935_4f5b_49ef_8949_a6af2a37957f_a1
      K hK hV
  have hLK : L = K := hMax L hKL hL
  rw [← hLK]
  exact hCount