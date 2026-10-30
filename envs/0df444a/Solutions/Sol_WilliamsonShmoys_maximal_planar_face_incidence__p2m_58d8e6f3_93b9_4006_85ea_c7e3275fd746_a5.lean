-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_incidence__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:18:47.277995+00:00
-- url     : https://prove2.me/submissions/9cacfef5-6fa1-4ba6-acf7-ffdef3811b1c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_7d7aec35_2e39_4f0c_96ea_78f8bd4c0509_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = L.edgeSet.ncard + 2) :
    3 * f = 2 * L.edgeSet.ncard := by
  have hEdge := WilliamsonShmoys.maximal_planar_edge_count__p2m_7d7aec35_2e39_4f0c_96ea_78f8bd4c0509_a1
    L hL hMax hCard
  omega