-- Prove2me | solution 1 for WilliamsonShmoys.face_count_equations_edge_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:03:21.783407+00:00
-- url     : https://prove2.me/submissions/6fd2e2ec-fdf7-42ca-a5df-9189ba5833e3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] {L : SimpleGraph V}
    (f : ℕ)
    (hEuler : L.edgeSet.ncard + 2 = Fintype.card V + f)
    (hIncidence : 3 * f = 2 * L.edgeSet.ncard) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  omega