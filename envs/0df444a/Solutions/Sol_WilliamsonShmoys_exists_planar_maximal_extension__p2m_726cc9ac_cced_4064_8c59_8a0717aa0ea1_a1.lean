-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_maximal_extension__p2m_726cc9ac_cced_4064_8c59_8a0717aa0ea1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:59:27.846341+00:00
-- url     : https://prove2.me/submissions/da3c0540-a5a3-49da-b38e-bafbcabe7522

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V),
        (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨le_rfl, hH⟩
  obtain ⟨K, hKm, hKmax⟩ :=
    Finset.exists_max_image S (fun G : SimpleGraph V => G.edgeSet.ncard) hS
  have hKprop : H ≤ K ∧ HasPlanarDrawingOn K :=
    (Finset.mem_filter.mp hKm).2
  refine ⟨K, ?_, hKprop.2, ?_, ?_⟩
  · intro u v huv
    exact (SimpleGraph.le_iff_adj.mp hKprop.1) u v huv
  · intro L hKL hL
    have hHL : H ≤ L := le_trans hKprop.1 hKL
    have hLmem : L ∈ S := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHL, hL⟩
    exact hKmax L hLmem
  · exact Set.ncard_mono (SimpleGraph.edgeSet_subset_edgeSet.mpr hKprop.1)