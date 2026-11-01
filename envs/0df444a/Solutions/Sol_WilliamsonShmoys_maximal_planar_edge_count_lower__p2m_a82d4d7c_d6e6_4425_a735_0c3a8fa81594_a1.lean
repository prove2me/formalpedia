-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_a82d4d7c_d6e6_4425_a735_0c3a8fa81594_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:53.752042+00:00
-- url     : https://prove2.me/submissions/cf5d416a-2429-4c6a-bced-51b91935ab52

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_3cf9c867_dcef_4284_9c77_b8f72e798b36_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  classical
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_3cf9c867_dcef_4284_9c77_b8f72e798b36_a2
      K hcard hK
  have hLK : L ≤ K := hmax L hKL hL
  have heq : L = K := le_antisymm hLK hKL
  rw [← heq]
  omega