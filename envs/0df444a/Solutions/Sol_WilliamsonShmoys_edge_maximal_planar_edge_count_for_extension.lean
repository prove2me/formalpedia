-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count_for_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:07:03.026662+00:00
-- url     : https://prove2.me/submissions/42edb8d6-6067-4aae-90b3-0225fe99e1d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_dc0151f5
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
      J.edgeSet ⊆ K.edgeSet → K.edgeSet = J.edgeSet) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hTri⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition_dc0151f5 J hJ hmax hV
  omega