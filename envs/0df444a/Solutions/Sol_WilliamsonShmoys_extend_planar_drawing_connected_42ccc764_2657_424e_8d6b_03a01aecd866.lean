-- Prove2me | solution 1 for WilliamsonShmoys.extend_planar_drawing_connected_42ccc764_2657_424e_8d6b_03a01aecd866
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:18:09.08361+00:00
-- url     : https://prove2.me/submissions/48aec252-ac33-4d76-adb2-8857c19c10d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_extend_planar_drawing_connected_with_linear_edge_additions

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    exists H : SimpleGraph V,
      Z.edgeSet ⊆ H.edgeSet ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Z.edgeSet.ncard <= H.edgeSet.ncard := by
  obtain ⟨H, hsub, hconn, hdraw, _hupper⟩ :=
    WilliamsonShmoys.extend_planar_drawing_connected_with_linear_edge_additions
      Z hV hZ
  exact ⟨H, hsub, hconn, hdraw, Set.ncard_mono hsub⟩