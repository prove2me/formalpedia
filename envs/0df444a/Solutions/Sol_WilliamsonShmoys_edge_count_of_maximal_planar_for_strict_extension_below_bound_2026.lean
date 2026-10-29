-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_for_strict_extension_below_bound_2026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:33:31.368211+00:00
-- url     : https://prove2.me/submissions/cc94a7e5-2020-4c90-9507-f1e7ee9bc368
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_certificate_2026

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall H : SimpleGraph V, K <= H -> HasPlanarDrawingOn H -> H = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_count_certificate_2026 K hK hCard hMax
  omega