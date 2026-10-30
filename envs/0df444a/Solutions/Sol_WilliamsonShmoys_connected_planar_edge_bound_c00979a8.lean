-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_c00979a8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:48:30.828883+00:00
-- url     : https://prove2.me/submissions/3f2a9393-605d-40ef-8630-fc3413d24932

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_maximal_extension_c00979a8
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_c00979a8

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLconn, hLdraw, hmax, hcard⟩ :=
    WilliamsonShmoys.connected_planar_maximal_extension_c00979a8
      K hV hconn hK
  have hbound := WilliamsonShmoys.maximal_planar_edge_bound_c00979a8
    L hV hLconn hLdraw hmax
  omega