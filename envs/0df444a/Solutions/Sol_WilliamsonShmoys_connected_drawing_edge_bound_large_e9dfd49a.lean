-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_edge_bound_large_e9dfd49a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:42:15.11247+00:00
-- url     : https://prove2.me/submissions/56f3a3c5-3b9f-4610-a8cd-1a0f1f2ba0ed

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_triangulated

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    (G.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨H, hGH, hHPlanar, hHCard⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_triangulated G hG hConnected hCard
  have hsubset : G.edgeSet ⊆ H.edgeSet :=
    (SimpleGraph.edgeSet_subset_edgeSet).2 hGH
  have hMonoNat : G.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_le_ncard hsubset
  have hMono : (G.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) := by
    exact_mod_cast hMonoNat
  rw [hHCard] at hMono
  exact hMono