-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:11:56.253802+00:00
-- url     : https://prove2.me/submissions/f31040a0-ca94-48f4-af3f-f158011d87bb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hle, hcard, _hdrawK⟩ :=
    WilliamsonShmoys.connected_planar_triangulation_augmentation H hdraw hconn hV
  omega