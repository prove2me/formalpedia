-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_a8cccb55
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:53:15.121249+00:00
-- url     : https://prove2.me/submissions/f2d4fa87-6546-42e1-830d-50dcedab84b0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : W.Connected)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    W.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hWH, hdrawH, hmaxH, hcardWH⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d W hW
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d H hV hdrawH hmaxH
  omega