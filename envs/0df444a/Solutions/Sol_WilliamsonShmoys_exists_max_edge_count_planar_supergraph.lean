-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_edge_count_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:51:25.985157+00:00
-- url     : https://prove2.me/submissions/5272abf7-82e5-4069-911b-11d478864ca7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_max_edge_count_in_finset

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet ⊆ H.edgeSet ∧
      (∀ J : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn J →
        H.edgeSet ⊆ J.edgeSet →
        J.edgeSet.ncard ≤ H.edgeSet.ncard) := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun G =>
    WilliamsonShmoys.HasPlanarDrawingOn G ∧ K.edgeSet ⊆ G.edgeSet
  have hKmem : K ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hK, Set.Subset.rfl⟩
  have hS : S.Nonempty := ⟨K, hKmem⟩
  obtain ⟨H, hHm, hmax⟩ :=
    WilliamsonShmoys.exists_max_edge_count_in_finset S hS
  have hHprops : WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet ⊆ H.edgeSet := by
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hHm
  refine ⟨H, hHprops.1, hHprops.2, ?_⟩
  intro J hJ hHJ
  apply hmax J
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hJ, Set.Subset.trans hHprops.2 hHJ⟩