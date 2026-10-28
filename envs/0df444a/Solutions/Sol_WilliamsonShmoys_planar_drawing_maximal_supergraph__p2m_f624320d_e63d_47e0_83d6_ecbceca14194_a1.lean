-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_f624320d_e63d_47e0_83d6_ecbceca14194_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:06:00.231315+00:00
-- url     : https://prove2.me/submissions/10048fba-9c61-4466-8a4d-b7b882018922

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      M ≤ N ∧
      (∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N := by
  classical
  have hdraw_sub {A B : SimpleGraph V} (hAB : A ≤ B)
      (hB : WilliamsonShmoys.HasPlanarDrawingOn B) :
      WilliamsonShmoys.HasPlanarDrawingOn A := by
    rcases hB with ⟨p, arc, hp, hcurves, hcross⟩
    exact ⟨p, arc, hp,
      (fun u v huv hadj => hcurves u v huv (hAB hadj)),
      (fun u v x y huv hxy hadjU hadjX hne t ht s hs heq =>
        hcross u v x y huv hxy (hAB hadjU) (hAB hadjX) hne t ht s hs heq)⟩
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => M ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
  have hS : S.Nonempty := by
    refine ⟨M, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_rfl, hM⟩
  obtain ⟨N, hNS, hmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeSet.ncard) hS
  have hN : M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N :=
    (Finset.mem_filter.mp hNS).2
  refine ⟨N, ?_, hN.1, ?_, hN.2⟩
  · exact Set.ncard_mono (SimpleGraph.edgeSet_mono hN.1)
  · intro K hNK hK
    by_contra hKN
    have hltGraph : N < K := lt_of_le_not_ge hNK hKN
    have hltEdges : N.edgeSet ⊂ K.edgeSet := SimpleGraph.edgeSet_strict_mono hltGraph
    have hltCard : N.edgeSet.ncard < K.edgeSet.ncard := Set.ncard_lt_ncard hltEdges
    have hKmem : K ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨le_trans hN.1 hNK, hK⟩
    exact (not_lt_of_ge (hmax K hKmem)) hltCard