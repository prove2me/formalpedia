-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:58.487236+00:00
-- url     : https://prove2.me/submissions/38788065-9920-450f-a5fb-599e7f69ca2b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet = N.edgeSet := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun G =>
    M.edgeSet ⊆ G.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨M, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨subset_rfl, hM⟩
  obtain ⟨N, hN, hmax⟩ :=
    S.exists_max_image (fun G : SimpleGraph V => G.edgeFinset.card) hS
  have hNmem := (Finset.mem_filter.mp hN).2
  refine ⟨N, hNmem.1, hNmem.2, ?_⟩
  intro K hNK hKdraw
  have hMK : M.edgeSet ⊆ K.edgeSet := hNmem.1.trans hNK
  have hKmem : K ∈ S := by
    apply Finset.mem_filter.mpr
    constructor
    · simp
    · exact ⟨hMK, hKdraw⟩
  have hcard : K.edgeFinset.card ≤ N.edgeFinset.card := hmax K hKmem
  have hsub : N.edgeFinset ⊆ K.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr
      (hNK (SimpleGraph.mem_edgeFinset.mp he))
  have hfin : N.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have hsets := congrArg (fun s : Finset (Sym2 V) => (s : Set (Sym2 V))) hfin
  simpa only [SimpleGraph.coe_edgeFinset] using hsets.symm