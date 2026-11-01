-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:15:46.568708+00:00
-- url     : https://prove2.me/submissions/45dfff1c-926c-4ef4-bbc6-435942959ce6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨K, ?_⟩
    simp [S, hK]
  obtain ⟨M, hMmem, hMmax⟩ :=
    Finset.exists_max_image S (fun G : SimpleGraph V => G.edgeFinset.card) hS
  have hKM : K ≤ M := (Finset.mem_filter.mp hMmem).2.1
  have hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M :=
    (Finset.mem_filter.mp hMmem).2.2
  refine ⟨M, hKM, hMdraw, ?_⟩
  intro N hMN hNdraw
  have hNmem : N ∈ S := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · exact ⟨le_trans hKM hMN, hNdraw⟩
  have hmax := hMmax N hNmem
  have hsub : M.edgeFinset ⊆ N.edgeFinset :=
    SimpleGraph.edgeFinset_mono hMN
  have hcard : M.edgeFinset.card = N.edgeFinset.card :=
    Nat.le_antisymm (Finset.card_le_card hsub) hmax
  have hedges : M.edgeFinset = N.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  exact (SimpleGraph.edgeFinset_inj.mp hedges).symm