-- Prove2me | solution 1 for WilliamsonShmoys.strict_graph_extension_edge_ncard__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:33:07.638371+00:00
-- url     : https://prove2.me/submissions/f9dc6579-1ae1-4516-a9a8-29bf39530b8b

import Mathlib

theorem solution {V : Type} [Fintype V] [DecidableEq V] {G L : SimpleGraph V} (h : G < L) : G.edgeSet.ncard < L.edgeSet.ncard := by
  apply Set.ncard_lt_ncard
  · refine Set.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeSet_mono h.le, ?_⟩
    intro heq
    apply h.ne
    ext u v
    have hmem := congrArg (fun s : Set (Sym2 V) => Sym2.mk u v ∈ s) heq
    simpa [SimpleGraph.mem_edgeSet] using hmem
  · exact Set.toFinite _