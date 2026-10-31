-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:48:07.848466+00:00
-- url     : https://prove2.me/submissions/edafaa31-4116-48ae-8c7a-f9a9ed6e794c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_f1bb3fc5_14ed_4f61_8573_9a7a487e7a06_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_f1bb3fc5_14ed_4f61_8573_9a7a487e7a06_a1 K hK hV
  have hLK : L ≤ K := hmax L hKL hL
  have hEq : L = K := le_antisymm hLK hKL
  simpa [hEq] using hcount