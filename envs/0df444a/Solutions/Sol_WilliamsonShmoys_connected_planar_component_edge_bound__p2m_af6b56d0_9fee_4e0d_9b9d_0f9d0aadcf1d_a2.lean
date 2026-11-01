-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_component_edge_bound__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:11:59.828324+00:00
-- url     : https://prove2.me/submissions/35ae6b47-9f03-416c-974d-47f80075a518
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_spanning_triangulation__p2m_cc516969_790b_410d_8fc5_8fd17bba7f5b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {U : Type} [Fintype U] [LinearOrder U]
    (G : SimpleGraph U) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card U) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card U := by
  obtain ⟨H, hle, hprops⟩ :=
    WilliamsonShmoys.spanning_triangulation__p2m_cc516969_790b_410d_8fc5_8fd17bba7f5b_a1
      G hdraw hconn hcard
  rcases hprops with ⟨_hdrawH, htri⟩
  calc
    G.edgeSet.ncard + 6 ≤ H.edgeSet.ncard + 6 := by
      exact Nat.add_le_add_right
        (Set.ncard_mono (SimpleGraph.edgeSet_mono hle)) 6
    _ = 3 * Fintype.card U := htri