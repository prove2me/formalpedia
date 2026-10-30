-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximality__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:35:07.829081+00:00
-- url     : https://prove2.me/submissions/2ae4a4c6-98c1-470d-aa49-86aaaa3a6e05

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet ⊆ K.edgeSet ∧
      ∀ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeSet ⊆ L.edgeSet →
        L.edgeSet ⊆ K.edgeSet := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => WilliamsonShmoys.HasPlanarDrawingOn G ∧
      H.edgeSet ⊆ G.edgeSet
  have hne : candidates.Nonempty := by
    refine ⟨H, ?_⟩
    simp [candidates, hH]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image candidates (fun G => G.edgeFinset.card) hne
  rcases Finset.mem_filter.mp hKmem with ⟨_, hKplanar, hHK⟩
  refine ⟨K, hKplanar, hHK, ?_⟩
  intro L hLplanar hKL
  by_contra hLK
  have hKLfin : K.edgeFinset ⊆ L.edgeFinset := by
    intro e he
    apply SimpleGraph.mem_edgeFinset.mpr
    apply hKL
    exact SimpleGraph.mem_edgeFinset.mp he
  have hnot : ¬ L.edgeFinset ⊆ K.edgeFinset := by
    intro hsub
    apply hLK
    intro e he
    exact SimpleGraph.mem_edgeFinset.mp
      (hsub (SimpleGraph.mem_edgeFinset.mpr he))
  have hlt : K.edgeFinset.card < L.edgeFinset.card :=
    Finset.card_lt_card ⟨hKLfin, hnot⟩
  have hLmem : L ∈ candidates := by
    change L ∈ Finset.univ.filter
      (fun G : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn G ∧
        H.edgeSet ⊆ G.edgeSet)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ L, hLplanar, hHK.trans hKL⟩
  exact (not_le_of_gt hlt) (hKmax L hLmem)