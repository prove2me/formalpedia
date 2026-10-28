-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_ncard_planar_supergraph_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:23:31.236238+00:00
-- url     : https://prove2.me/submissions/8ce185b0-1064-424c-9a67-bac01012addb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, L ≤ N →
          WilliamsonShmoys.HasPlanarDrawingOn N →
            N.edgeSet.ncard ≤ M.edgeSet.ncard := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun M =>
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M)
  have hSne : S.Nonempty := by
    refine ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ L, le_rfl, hL⟩⟩
  obtain ⟨M, hM, hmax⟩ :=
    S.exists_max_image (fun G : SimpleGraph V => G.edgeSet.ncard) hSne
  refine ⟨M, (Finset.mem_filter.mp hM).2.1,
    (Finset.mem_filter.mp hM).2.2, ?_⟩
  intro N hLN hN
  exact hmax N (Finset.mem_filter.mpr ⟨Finset.mem_univ N, hLN, hN⟩)