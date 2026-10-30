-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_b456ae06_v4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:18:23.330951+00:00
-- url     : https://prove2.me/submissions/ca57d1c9-9b4e-495d-aba4-1518d12db929

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_count K hV hK hmax
  omega