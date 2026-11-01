-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_afb5df26_e4fb_4772_9aa3_0e4304c46b48_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:06:38.686208+00:00
-- url     : https://prove2.me/submissions/86f06d76-7a73-4a3b-8885-6f1d249c0185

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧ L ≤ M ∧
        ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N = M := by
  classical
  obtain ⟨M, hM, hmax⟩ := by
    apply Set.exists_max_image
      { G : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn G ∧ L ≤ G }
      (fun G => G.edgeFinset.card)
    · exact Set.toFinite _
    · exact ⟨L, hplanar, le_rfl⟩
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro N hN hMN
  have hEdges : M.edgeFinset = N.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le
    · exact SimpleGraph.edgeFinset_subset_edgeFinset.mpr hMN
    · exact hmax N ⟨hN, hM.2.trans hMN⟩
  exact (SimpleGraph.edgeFinset_inj.mp hEdges).symm
