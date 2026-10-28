-- Prove2me | solution 2 for WilliamsonShmoys.exists_maximal_planar_supergraph_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:41:56.242376+00:00
-- url     : https://prove2.me/submissions/77757b70-066f-4a64-b593-414a2f39e336

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
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V,
      LE.le W X ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      (forall Y : SimpleGraph V,
        LE.le X Y -> WilliamsonShmoys.HasPlanarDrawingOn Y -> Y = X) := by
  obtain ⟨N, h1, h2, h3, -⟩ := S191EY_ext W hW
  exact ⟨N, h1, h2, fun Y hY hd => le_antisymm (h3 Y hY hd) hY⟩
