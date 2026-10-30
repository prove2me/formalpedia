-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound_57594b84
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:54:51.704498+00:00
-- url     : https://prove2.me/submissions/4158fa45-bfc7-4495-8486-07297b39d397

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_maximal_extension_v2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_euler_v2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hSub, hDrawK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound_maximal_extension_v2 H hDraw
  have hKFinite : K.edgeSet.Finite := Set.toFinite _
  have hCardLE : H.edgeSet.ncard ≤ K.edgeSet.ncard :=
    Set.ncard_le_ncard hSub hKFinite
  have hK :=
    WilliamsonShmoys.planar_drawing_maximal_edge_count_euler_v2 K hDrawK hMax hCard
  omega