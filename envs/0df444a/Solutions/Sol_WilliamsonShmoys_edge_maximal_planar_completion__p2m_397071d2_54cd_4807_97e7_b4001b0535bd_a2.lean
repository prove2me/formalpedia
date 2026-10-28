-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_completion__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:33.047401+00:00
-- url     : https://prove2.me/submissions/bf05674a-9004-498b-99c5-178bf7face63

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) := by
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
  exact key (fun L => HasPlanarDrawingOn L) K hK
