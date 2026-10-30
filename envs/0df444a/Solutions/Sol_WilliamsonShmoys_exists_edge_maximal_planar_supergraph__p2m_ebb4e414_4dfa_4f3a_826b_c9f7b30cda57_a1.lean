-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_ebb4e414_4dfa_4f3a_826b_c9f7b30cda57_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:35:07.914445+00:00
-- url     : https://prove2.me/submissions/14a9341b-a625-49d6-95dd-f9e8a3ab8490

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V,
        H ≤ J →
        WilliamsonShmoys.HasPlanarDrawingOn J →
        J = H := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => M ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hAdmissible : admissible.Nonempty := by
    refine ⟨M, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ _, le_rfl, hDraw⟩
  obtain ⟨H, hHmem, hHmax⟩ :=
    Finset.exists_max_image admissible (fun G => G.edgeFinset.card) hAdmissible
  have hH := (Finset.mem_filter.mp hHmem).2
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro J hHJ hJDraw
  have hJmem : J ∈ admissible := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, le_trans hH.1 hHJ, hJDraw⟩
  have hEdgeSubset : H.edgeFinset ⊆ J.edgeFinset :=
    SimpleGraph.edgeFinset_mono hHJ
  have hEdgeCard : J.edgeFinset.card ≤ H.edgeFinset.card := hHmax J hJmem
  have hEdgeEq : H.edgeFinset = J.edgeFinset :=
    Finset.eq_of_subset_of_card_le hEdgeSubset hEdgeCard
  ext u v
  have h := congrArg (fun E : Finset (Sym2 V) => Sym2.mk u v ∈ E) hEdgeEq
  simpa using h.symm
