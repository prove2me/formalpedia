-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_edge_count_planar_supergraph__p2m_61d32ba8_63e6_4051_9eef_c43df50e222b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:16:02.801335+00:00
-- url     : https://prove2.me/submissions/76699c4a-f9f5-479a-b6f8-af8b7347e672

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
          M.edgeSet.ncard ≤ L.edgeSet.ncard := by
  classical
  let s : Finset (SimpleGraph V) :=
    Finset.univ.filter fun L => K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L
  have hK : K ∈ s := by
    simp [s, hDraw]
  obtain ⟨L, hL, hmax⟩ :=
    Finset.exists_max_image s (fun G => G.edgeSet.ncard) ⟨K, hK⟩
  have hLp : K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
    simpa [s] using hL
  refine ⟨L, hLp.1, hLp.2, ?_⟩
  intro M hKM hDrawM
  exact hmax M (by simp [s, hKM, hDrawM])