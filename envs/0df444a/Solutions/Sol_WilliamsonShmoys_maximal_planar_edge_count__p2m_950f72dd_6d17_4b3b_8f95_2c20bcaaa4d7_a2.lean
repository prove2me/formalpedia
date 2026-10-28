-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:01:32.701556+00:00
-- url     : https://prove2.me/submissions/65025711-db9d-456d-ba5c-58c162264b02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_bc55d69b_5743_4927_884d_0327a4a2fa7c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_bc55d69b_5743_4927_884d_0327a4a2fa7c_a1
      H hH hV
  have hKH : K ≤ H := hmax K hHK hK
  have hEq : H = K := le_antisymm hHK hKH
  simpa [hEq] using hCount.symm