-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanar_extension_edgeCount__p2m_7a506924_211f_41ba_877a_336e51746219_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:14:57.36118+00:00
-- url     : https://prove2.me/submissions/45f35b12-f9a2-4f82-896e-1a740cebcf09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet ∧
      HasPlanarDrawingOn U ∧ U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hTU, hU, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1 T hT
  refine ⟨U, hTU, hU, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_6cde29f9_0337_48f4_829a_b67e3b72f2a9_a1 U hU hmax hV