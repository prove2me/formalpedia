-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_edge_bound_v2_planar_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:54:13.739332+00:00
-- url     : https://prove2.me/submissions/99aa192b-34bd-4927-b845-438f218cd96f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_to_edge_maximal
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hH, hcard, hHconn, hmax⟩ :=
    WilliamsonShmoys.planar_extension_to_edge_maximal K hK hconn
  refine ⟨H, hKH, hH, hcard, ?_⟩
  exact WilliamsonShmoys.edge_maximal_planar_edge_count H hV hH hHconn hmax