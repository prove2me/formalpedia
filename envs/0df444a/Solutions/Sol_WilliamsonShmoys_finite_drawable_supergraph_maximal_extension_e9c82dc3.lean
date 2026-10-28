-- Prove2me | solution 1 for WilliamsonShmoys.finite_drawable_supergraph_maximal_extension_e9c82dc3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:27:23.565994+00:00
-- url     : https://prove2.me/submissions/08276e7b-f779-4da8-a326-934b9cf98149

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun K => M ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K)
  have hS : S.Nonempty := ⟨M, by simp [S, hM]⟩
  obtain ⟨N, hN, hmax⟩ := Finset.exists_max_image S (fun K => K.edgeSet.ncard) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hN hmax
  refine ⟨N, hN.1, hN.2, ?_, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hN.1) (Set.toFinite _)⟩
  intro K hNK hK
  have h1 := hmax K ⟨hN.1.trans hNK, hK⟩
  have hsub : N.edgeSet ⊆ K.edgeSet := SimpleGraph.edgeSet_mono hNK
  have heq : N.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsub h1 (Set.toFinite _)
  exact le_of_eq (SimpleGraph.edgeSet_injective heq).symm
