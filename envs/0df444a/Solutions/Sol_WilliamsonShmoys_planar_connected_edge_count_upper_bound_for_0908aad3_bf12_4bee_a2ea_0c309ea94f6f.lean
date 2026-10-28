-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_count_upper_bound_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:19:43.829483+00:00
-- url     : https://prove2.me/submissions/e5a2390a-15a0-4c8f-b4b2-190a7cced6d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_upper_bound_maximal_extension_562a75e6
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_upper_bound_maximal_edge_count_562a75e6

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hV : 3 ≤ Fintype.card V) :
    (L.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨H, hLH, hdrawH, hconnH, hmax⟩ :=
    WilliamsonShmoys.planar_connected_edge_count_upper_bound_maximal_extension_562a75e6
      L hdraw hconn hV
  have hH :=
    WilliamsonShmoys.planar_connected_edge_count_upper_bound_maximal_edge_count_562a75e6
      H hdrawH hconnH hV hmax
  have hcard : L.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hLH)
  exact (Int.ofNat_le.mpr hcard).trans hH