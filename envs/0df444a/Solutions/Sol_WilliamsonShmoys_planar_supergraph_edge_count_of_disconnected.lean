-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_of_disconnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:11:33.926111+00:00
-- url     : https://prove2.me/submissions/55a5f5d8-6bf7-44c8-96a3-0b41c9f15411
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_disconnected_single_edge_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ ∀ u v, Relation.ReflTransGen H.Adj u v) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard < K.edgeSet.ncard := by
  obtain ⟨K, hsub, hextra, hK⟩ :=
    WilliamsonShmoys.planar_disconnected_single_edge_augmentation H hH hV hdisconnected
  obtain ⟨e, he, hedgeSet⟩ := hextra
  refine ⟨K, hsub, hK, ?_⟩
  rw [hedgeSet, Set.ncard_insert_of_notMem he]
  exact Nat.lt_succ_self _