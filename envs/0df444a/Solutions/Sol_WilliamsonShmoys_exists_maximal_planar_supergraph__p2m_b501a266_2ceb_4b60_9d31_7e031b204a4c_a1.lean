-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b501a266_2ceb_4b60_9d31_7e031b204a4c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:51:06.820317+00:00
-- url     : https://prove2.me/submissions/22bfd4f9-1fba-4cd0-ba10-03502e2cba07

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ M : SimpleGraph V,
      T.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊆ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet ⊆ M.edgeSet := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => T ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hne : admissible.Nonempty := by
    refine ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨le_rfl, hT⟩
  obtain ⟨M, hM, hmax⟩ :=
    Finset.exists_max_image admissible (fun G => G.edgeSet.encard) hne
  have hMT : T ≤ M := (Finset.mem_filter.mp hM).2.1
  have hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M :=
    (Finset.mem_filter.mp hM).2.2
  refine ⟨M, SimpleGraph.edgeSet_subset_edgeSet.mpr hMT, hMplanar, ?_⟩
  intro N hMN hNplanar
  have hTN : T ≤ N :=
    le_trans hMT (SimpleGraph.edgeSet_subset_edgeSet.mp hMN)
  have hNmem : N ∈ admissible :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTN, hNplanar⟩
  by_contra hNM
  have hproper : M.edgeSet ⊂ N.edgeSet := ⟨hMN, hNM⟩
  have hlt : M.edgeSet.encard < N.edgeSet.encard :=
    Set.encard_strictMono hproper
  exact (not_le_of_gt hlt) (hmax N hNmem)