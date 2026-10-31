-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:35:53.413047+00:00
-- url     : https://prove2.me/submissions/33449f5f-9baf-4a06-afb4-ced2273ba3cc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => M ≤ G ∧ HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨M, ?_⟩
    simp [S, hM]
  obtain ⟨H, hHmem, hHmax⟩ := S.exists_maximal hS
  have hHM : M ≤ H := (Finset.mem_filter.mp hHmem).2.1
  have hdrawH : HasPlanarDrawingOn H := (Finset.mem_filter.mp hHmem).2.2
  refine ⟨H, hHM, hdrawH, ?_⟩
  intro K hHK hdrawK
  have hKmem : K ∈ S := by
    simp [S, hHM.trans hHK, hdrawK]
  have hKH : K ≤ H := hHmax hKmem hHK
  exact le_antisymm hKH hHK
