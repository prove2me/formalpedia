-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:41:11.207487+00:00
-- url     : https://prove2.me/submissions/2c036580-da45-4739-aae9-76e71b338985

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ N.edgeSet.ncard := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => M ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨M, ?_⟩
    simp [S, hM]
  obtain ⟨N, hN, hmax⟩ :=
    Finset.exists_max_image S (fun G : SimpleGraph V => G.edgeSet.ncard) hS
  refine ⟨N, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hN).2.1
  · exact (Finset.mem_filter.mp hN).2.2
  · intro K hNK hK
    have hKmem : K ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ K, ?_⟩
      constructor
      · exact le_trans (Finset.mem_filter.mp hN).2.1 hNK
      · exact hK
    exact hmax K hKmem