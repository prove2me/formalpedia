-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_triangulatedExtension_edgeCount__p2m_07bf48fb_9eeb_4a56_867a_2639c9be995e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:12.332205+00:00
-- url     : https://prove2.me/submissions/f8546121-33b6-45ff-a8bb-39c0d71574c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximalSupergraph__p2m_998ffb22_8369_4943_b685_9f335822785c_a1
import Theorems.Thm_WilliamsonShmoys_maximalPlanar_edgeCount__p2m_998ffb22_8369_4943_b685_9f335822785c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, M.edgeSet.ncard ≤ T.edgeSet.ncard ∧
      HasPlanarDrawingOn T ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hcount, hsub, hdraw, hmax⟩ :=
    WilliamsonShmoys.planarDrawingOn_maximalSupergraph__p2m_998ffb22_8369_4943_b685_9f335822785c_a1 M hM hV
  have htri := WilliamsonShmoys.maximalPlanar_edgeCount__p2m_998ffb22_8369_4943_b685_9f335822785c_a1 T hdraw hV hmax
  exact ⟨T, hcount, hdraw, htri⟩