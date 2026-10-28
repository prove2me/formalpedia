-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_v4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:47:53.616508+00:00
-- url     : https://prove2.me/submissions/ee32c06f-8e8e-498b-9cf6-7ca67b414fae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_upper_bound_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    (L.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨H, hLH, hHconn, hHdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
      L hdraw (by omega)
  have hmonoNat : L.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hLH)
  have hmono : (L.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) := by
    exact_mod_cast hmonoNat
  have hbound :=
    WilliamsonShmoys.planar_connected_edge_count_upper_bound_for_0908aad3_bf12_4bee_a2ea_0c309ea94f6f
      H hHdraw hHconn hV
  omega