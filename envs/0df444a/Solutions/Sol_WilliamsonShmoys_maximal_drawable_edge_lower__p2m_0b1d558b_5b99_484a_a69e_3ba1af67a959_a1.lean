-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_lower__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:45:24.444279+00:00
-- url     : https://prove2.me/submissions/6f54644b-0c3c-48d4-af3d-983eea9e5987

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : T.Connected)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ S : SimpleGraph V, T ≤ S → HasPlanarDrawingOn S → S = T) :
    3 * Fintype.card V - 6 ≤ T.edgeSet.ncard := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition T hT hmax hV
  omega