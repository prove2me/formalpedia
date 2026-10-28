-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_finite_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:36:52.533553+00:00
-- url     : https://prove2.me/submissions/1470a304-94dd-4b7d-97d2-6b010c2687e5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem S191EY_ext
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

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      And (H <= K)
        (And (WilliamsonShmoys.HasPlanarDrawingOn K)
          (And (forall K' : SimpleGraph V, K <= K' ->
            WilliamsonShmoys.HasPlanarDrawingOn K' -> K' = K)
            (H.edgeSet.ncard <= K.edgeSet.ncard))) := by
  obtain ⟨N, h1, h2, h3, h4⟩ := S191EY_ext H hHplanar
  exact ⟨N, h1, h2, fun K' hK' hd => le_antisymm (h3 K' hK' hd) hK', h4⟩
