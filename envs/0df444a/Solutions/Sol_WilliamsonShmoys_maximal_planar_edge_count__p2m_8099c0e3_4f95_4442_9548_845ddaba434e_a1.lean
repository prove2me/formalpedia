-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:30:57.43566+00:00
-- url     : https://prove2.me/submissions/63c4dfdf-d314-46cc-b338-ad9352862615

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations__p2m_529ff6c9_d746_4547_9934_f47cc51c6339_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hTriangular⟩ :=
    WilliamsonShmoys.maximal_planar_face_equations__p2m_529ff6c9_d746_4547_9934_f47cc51c6339_a1
      L hDraw hMax hV
  omega