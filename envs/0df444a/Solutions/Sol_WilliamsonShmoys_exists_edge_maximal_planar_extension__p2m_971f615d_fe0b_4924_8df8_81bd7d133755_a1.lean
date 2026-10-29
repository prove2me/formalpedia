-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_971f615d_fe0b_4924_8df8_81bd7d133755_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:53:31.444711+00:00
-- url     : https://prove2.me/submissions/bdcb89f6-a7af-4806-a952-b44b9f177a1f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  let S : Set (SimpleGraph V) :=
    {K | G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K}
  have hSfin : S.Finite :=
    Set.finite_univ.subset (by
      intro K hK
      exact Set.mem_univ K)
  have hSne : S.Nonempty := ⟨G, le_rfl, hG⟩
  obtain ⟨K, hKmax⟩ := hSfin.exists_maximal hSne
  rcases hKmax.1 with ⟨hGK, hKD⟩
  refine ⟨K, hGK, hKD, ?_⟩
  intro L hKL hLD
  have hLS : L ∈ S := ⟨hGK.trans hKL, hLD⟩
  have hLK : L ≤ K := hKmax.2 hLS hKL
  exact le_antisymm hLK hKL