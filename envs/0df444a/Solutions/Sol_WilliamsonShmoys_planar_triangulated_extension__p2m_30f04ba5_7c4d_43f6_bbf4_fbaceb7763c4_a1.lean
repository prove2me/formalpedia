-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulated_extension__p2m_30f04ba5_7c4d_43f6_bbf4_fbaceb7763c4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:39:45.419981+00:00
-- url     : https://prove2.me/submissions/f318a874-ac15-4399-a268-3ca10302f190

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    exists M : SimpleGraph V, L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  cases WilliamsonShmoys.exists_maximal_drawable_extension__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1
      L hDraw with
  | intro M hRest =>
    cases hRest with
    | intro hLM hRest =>
      cases hRest with
      | intro hMDraw hMax =>
        have hCount :=
          WilliamsonShmoys.maximal_drawable_edge_count__p2m_28646a36_1b88_4c0c_9520_4ba110528cb4_a1
            M hMDraw hMax hCard
        exact Exists.intro M (And.intro hLM (And.intro hMDraw hCount))