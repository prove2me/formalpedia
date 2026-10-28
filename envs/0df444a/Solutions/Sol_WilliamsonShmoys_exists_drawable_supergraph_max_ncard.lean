-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_supergraph_max_ncard
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:40:27.675864+00:00
-- url     : https://prove2.me/submissions/30546a69-553c-4ce6-a360-10fa8fece935

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, L ≤ N →
          WilliamsonShmoys.HasPlanarDrawingOn N →
            N.edgeSet.ncard ≤ M.edgeSet.ncard := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨L, ?_⟩
    simp [S, hLdraw]
  obtain ⟨M, hM, hmax⟩ := S.exists_max_image (fun G => G.edgeSet.ncard) hS
  refine ⟨M, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hM).2.1
  · exact (Finset.mem_filter.mp hM).2.2
  · intro N hLN hNdraw
    exact hmax N (by simp [S, hLN, hNdraw])