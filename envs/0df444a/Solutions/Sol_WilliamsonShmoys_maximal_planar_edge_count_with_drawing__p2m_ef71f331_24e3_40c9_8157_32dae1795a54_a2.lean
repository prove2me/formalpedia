-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_with_drawing__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:32:17.234089+00:00
-- url     : https://prove2.me/submissions/aa25313c-bebb-4fa0-8988-951b313ea3c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_exact_edge_count__p2m_6cb4ee63_7c67_490c_a2c2_32ddc6101392_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmaximal : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet → HasPlanarDrawingOn M → M.edgeSet = L.edgeSet) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.planar_completion_exact_edge_count__p2m_6cb4ee63_7c67_490c_a2c2_32ddc6101392_a1
      L hL hV
  have heq := hmaximal M hLM hM
  rw [← heq]
  exact hcount