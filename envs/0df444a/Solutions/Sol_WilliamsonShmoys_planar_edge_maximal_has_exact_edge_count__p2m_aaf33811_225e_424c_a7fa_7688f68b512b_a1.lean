-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_has_exact_edge_count__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:14.718192+00:00
-- url     : https://prove2.me/submissions/2093e92e-5271-4220-ac11-61f863e9e28d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_b1659f81_1f0c_4922_9013_d0dbf115cc22_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_b1659f81_1f0c_4922_9013_d0dbf115cc22_a2
      L hcard hL
  have hEq : M = L := hmax M hLM hM
  rw [hEq] at hcount
  exact hcount