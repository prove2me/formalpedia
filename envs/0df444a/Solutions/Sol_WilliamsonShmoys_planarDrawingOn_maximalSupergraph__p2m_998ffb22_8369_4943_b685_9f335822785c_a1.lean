-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_maximalSupergraph__p2m_998ffb22_8369_4943_b685_9f335822785c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:32.657993+00:00
-- url     : https://prove2.me/submissions/e1e47c97-9869-490a-a358-0d8571fd8389

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximal_supergraph_family__p2m_d834da15_b585_41bf_a8ee_e18eb971234e_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      M.edgeSet.ncard ≤ T.edgeSet.ncard ∧
      M.edgeSet ⊆ T.edgeSet ∧
      HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet →
        HasPlanarDrawingOn U → U.edgeSet ⊆ T.edgeSet := by
  obtain ⟨T, hcard, hsub, hdraw, hmax⟩ :=
    WilliamsonShmoys.planarDrawingOn_maximal_supergraph_family__p2m_d834da15_b585_41bf_a8ee_e18eb971234e_a1
      M HasPlanarDrawingOn hM
  exact ⟨T, hcard, hsub, hdraw, hmax⟩