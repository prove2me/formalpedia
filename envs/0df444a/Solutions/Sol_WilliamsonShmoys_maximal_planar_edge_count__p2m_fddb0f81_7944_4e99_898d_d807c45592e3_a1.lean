-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T18:37:35.657774+00:00
-- url     : https://prove2.me/submissions/5912d3f8-00c4-4aa4-ba48-58e7caa77ea0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hsub, hMplanar, hMlower⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_lower_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
      L hV hL
  have hEq : M.edgeSet = L.edgeSet := hmax M hsub hMplanar
  have hLower : 3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
    simpa [hEq] using hMlower
  have hUpper : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_98c8bf31_da7f_4753_99f2_642509315647_a1
      L hV hL
  omega