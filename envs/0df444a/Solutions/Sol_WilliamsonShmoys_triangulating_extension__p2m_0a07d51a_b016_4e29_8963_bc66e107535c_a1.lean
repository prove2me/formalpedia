-- Prove2me | solution 1 for WilliamsonShmoys.triangulating_extension__p2m_0a07d51a_b016_4e29_8963_bc66e107535c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:11:31.741856+00:00
-- url     : https://prove2.me/submissions/ea725797-15f9-4ae7-9337-a769aa2dc291
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension__p2m_c20796cc_c576_4992_b291_9784ec70fc6e_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_c20796cc_c576_4992_b291_9784ec70fc6e_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       3 * Fintype.card V = L.edgeFinset.card + 6) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_extension__p2m_c20796cc_c576_4992_b291_9784ec70fc6e_a1 K hK
  have hedge :=
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_c20796cc_c576_4992_b291_9784ec70fc6e_a1
      L hV hL hmax
  exact ⟨L, hKL, hL, hedge⟩