-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:32:30.33257+00:00
-- url     : https://prove2.me/submissions/34f15bcf-4de9-468f-8a3b-b3b28f92fabc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count__p2m_c2eda16e_e381_4c67_86d8_74bdc260bd3a_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hsub, hMdraw, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_c2eda16e_e381_4c67_86d8_74bdc260bd3a_a1
      L hV hDraw
  have hEq := hmax M hsub hMdraw
  rw [← hEq]
  exact le_of_eq hcount