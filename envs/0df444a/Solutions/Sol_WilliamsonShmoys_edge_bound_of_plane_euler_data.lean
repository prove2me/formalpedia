-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_plane_euler_data
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:07:08.127839+00:00
-- url     : https://prove2.me/submissions/4289a791-71fd-4670-9759-4e83b318a548

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlaneEulerData

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hData : WilliamsonShmoys.HasPlaneEulerData G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  classical
  rcases hData with ⟨F, hF, hEuler, hFace⟩
  letI : Fintype F := hF
  omega