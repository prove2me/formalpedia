-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2732a158_7c47_4798_8446_4021e87baee8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:52:21.800883+00:00
-- url     : https://prove2.me/submissions/cd7facc0-b756-48de-b3be-1759b9a9d139

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hTplanar : HasPlanarDrawingOn T)
    (hmax : ∀ S : SimpleGraph V, T ≤ S → HasPlanarDrawingOn S → S = T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition T hTplanar hmax hV
  omega