-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:34.731857+00:00
-- url     : https://prove2.me/submissions/0ad221ff-09e7-4624-88c3-1ae7748a799f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    exists N : SimpleGraph V,
      M <= N /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      forall K : SimpleGraph V,
        N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = N := by
  classical
  have key : ∀ (P : SimpleGraph V → Prop) (T : SimpleGraph V), P T →
      ∃ L, T ≤ L ∧ P L ∧ ∀ M, L ≤ M → P M → M = L := by
    intro P T hT
    have hfin : {L : SimpleGraph V | T ≤ L ∧ P L}.Finite := Set.toFinite _
    obtain ⟨L, hL, hmax⟩ := Set.exists_max_image {L : SimpleGraph V | T ≤ L ∧ P L}
      (fun L => L.edgeSet.ncard) hfin ⟨T, le_rfl, hT⟩
    refine ⟨L, hL.1, hL.2, ?_⟩
    intro M hLM hM
    have hc : M.edgeSet.ncard ≤ L.edgeSet.ncard := hmax M ⟨le_trans hL.1 hLM, hM⟩
    have hsub : L.edgeSet ⊆ M.edgeSet := SimpleGraph.edgeSet_mono hLM
    have hfM : M.edgeSet.Finite := Set.toFinite _
    have := Set.eq_of_subset_of_ncard_le hsub hc hfM
    exact (SimpleGraph.edgeSet_inj.mp this.symm)
  exact key (fun L => WilliamsonShmoys.HasPlanarDrawingOn L) M hM
