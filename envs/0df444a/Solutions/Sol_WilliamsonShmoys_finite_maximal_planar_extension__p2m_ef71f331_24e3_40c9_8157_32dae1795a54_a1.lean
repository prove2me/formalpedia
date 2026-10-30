-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_planar_extension__p2m_ef71f331_24e3_40c9_8157_32dae1795a54_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:29:16.254572+00:00
-- url     : https://prove2.me/submissions/7748d26f-dec7-4f53-823a-512c98ac6fb5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_maximal_simpleGraph_extension__p2m_5ee8e196_64c4_419c_bd20_94ce32b8d5fd_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet → HasPlanarDrawingOn M →
        M.edgeSet = L.edgeSet := by
  exact finite_maximal_simpleGraph_extension__p2m_5ee8e196_64c4_419c_bd20_94ce32b8d5fd_a1
    HasPlanarDrawingOn K hK