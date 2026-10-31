-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:34:24.469989+00:00
-- url     : https://prove2.me/submissions/dd1c43aa-b70a-4dc1-9abc-ae26ba101f69

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion__p2m_2881ff5d_60b0_4f02_aa50_a31ff757101b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    3 * Fintype.card V - 6 = N.edgeSet.ncard := by
  obtain ⟨K, hNK, hK, hKcard⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_2881ff5d_60b0_4f02_aa50_a31ff757101b_a1
      N hV hN
  have hKN : K ≤ N := hmax K hNK hK
  have hEq : K = N := le_antisymm hKN hNK
  simpa [hEq] using hKcard