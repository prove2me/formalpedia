-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_count_edge_bound__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:25:35.211561+00:00
-- url     : https://prove2.me/submissions/4630b806-fb9e-482b-b624-8cd622cf7d5c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V]
    (M : SimpleGraph V)
    (F : Type) [Fintype F]
    (hEuler : Fintype.card V + Fintype.card F = M.edgeSet.ncard + 2)
    (hInc : 3 * Fintype.card F <= 2 * M.edgeSet.ncard) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  omega