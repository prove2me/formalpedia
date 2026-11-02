-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:09:16.332197+00:00
-- url     : https://prove2.me/submissions/d66b3795-2577-46fe-997e-e6fc37c9b53d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_poset_maximal_element__p2m_75c86ecd_00c9_4da6_b3eb_332cdc8728f4_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V, G ≤ T ∧ HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T := by
  exact finite_poset_maximal_element__p2m_75c86ecd_00c9_4da6_b3eb_332cdc8728f4_a1
    (α := SimpleGraph V) (P := HasPlanarDrawingOn) G hG