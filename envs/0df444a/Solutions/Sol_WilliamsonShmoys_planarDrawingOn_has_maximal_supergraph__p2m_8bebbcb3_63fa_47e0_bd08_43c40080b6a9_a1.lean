-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_has_maximal_supergraph__p2m_8bebbcb3_63fa_47e0_bd08_43c40080b6a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:30:15.274576+00:00
-- url     : https://prove2.me/submissions/c22dce4d-6e94-4218-926a-ea152d165533

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => M ≤ G ∧ HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨M, ?_⟩
    simp [S, hM]
  obtain ⟨N, hN, hmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeSet.ncard) hS
  have hNM : M ≤ N := (Finset.mem_filter.mp hN).2.1
  have hNp : HasPlanarDrawingOn N := (Finset.mem_filter.mp hN).2.2
  have hMNcard : M.edgeSet.ncard ≤ N.edgeSet.ncard := by
    exact hmax M (by simp [S, hM])
  refine ⟨N, hNM, hNp, hMNcard, ?_⟩
  intro K hNK hKp
  have hKmem : K ∈ S := by
    simp [S, hNM.trans hNK, hKp]
  have hKNcard : K.edgeSet.ncard ≤ N.edgeSet.ncard := hmax K hKmem
  have hsets : N.edgeSet = K.edgeSet :=
    Set.eq_of_subset_of_ncard_le
      (SimpleGraph.edgeSet_subset_edgeSet.mpr hNK) hKNcard
  exact SimpleGraph.edgeSet_inj.mp hsets.symm