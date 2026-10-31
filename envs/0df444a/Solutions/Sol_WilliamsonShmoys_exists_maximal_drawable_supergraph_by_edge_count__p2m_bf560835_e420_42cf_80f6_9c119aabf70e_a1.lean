-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_by_edge_count__p2m_bf560835_e420_42cf_80f6_9c119aabf70e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:35:12.82888+00:00
-- url     : https://prove2.me/submissions/e3eddf30-102c-4225-b8d1-f789d85bca00

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet.ncard ≤ M.edgeSet.ncard) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => L ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hLmem : L ∈ candidates := by
    simp [candidates, hL]
  have hCandidates : candidates.Nonempty := ⟨L, hLmem⟩
  obtain ⟨M, hMmem, hmax⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeSet.ncard) hCandidates
  refine ⟨M, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hMmem).2.1
  · exact (Finset.mem_filter.mp hMmem).2.2
  · intro N hLN hN
    exact hmax N (by simp [candidates, hLN, hN])