-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_exact_edge_count__p2m_6cb4ee63_7c67_490c_a2c2_32ddc6101392_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:48:59.918289+00:00
-- url     : https://prove2.me/submissions/be404e20-39bc-4242-92f6-f0945533e73d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1
      L hL hV
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1
      M hM hV hMax
  exact ⟨M, hLM, hM, hCount⟩