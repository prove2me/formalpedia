-- Prove2me | solution 2 for WilliamsonShmoys.exists_drawable_completion_maximal_extension_for_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:53:33.005329+00:00
-- url     : https://prove2.me/submissions/e0e6f552-8bab-411d-80e2-1bb2572d6ca6

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
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V, N ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  obtain ⟨M, h1, h2, h3, -⟩ := S191EY_ext N hN
  exact ⟨M, h1, h2, fun K hK hd => le_antisymm (h3 K hK hd) hK⟩
