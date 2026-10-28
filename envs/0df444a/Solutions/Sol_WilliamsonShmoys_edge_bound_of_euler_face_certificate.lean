-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_euler_face_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:14:39.461223+00:00
-- url     : https://prove2.me/submissions/e76a483a-2850-4575-b028-d5453e29d5ec

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hV : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = K.edgeSet.ncard + 2)
    (hFaces : 3 * f ≤ 2 * K.edgeSet.ncard) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  have hEdges : H.edgeSet.ncard ≤ K.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hHK)
  omega