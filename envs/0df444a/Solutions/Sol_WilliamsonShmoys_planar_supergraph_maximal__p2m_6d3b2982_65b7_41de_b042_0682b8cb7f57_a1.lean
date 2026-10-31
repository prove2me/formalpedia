-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:30:44.578554+00:00
-- url     : https://prove2.me/submissions/b3e5153e-8ea5-4933-9234-531ebcd54448

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Finite.Lemmas
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V,
        P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q →
          Q.edgeSet.ncard ≤ P.edgeSet.ncard := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | N ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSN : N ∈ S := by
    simp [S, hN]
  obtain ⟨P, hP, hmax⟩ :=
    Set.exists_max_image S (fun G : SimpleGraph V => G.edgeSet.ncard)
      hSfinite ⟨N, hSN⟩
  refine ⟨P, hP.1, hP.2, ?_⟩
  intro Q hPQ hQ
  exact hmax Q ⟨hP.1.trans hPQ, hQ⟩