-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_finite
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:46:01.598486+00:00
-- url     : https://prove2.me/submissions/9f98b1f6-1eab-4156-854e-3af0dd6d01c6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_mono_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  obtain ⟨K, hHK, hK, hcard, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_of_finite_mono_edge_count
      WilliamsonShmoys.HasPlanarDrawingOn
      (fun {G F} hGF hF => by
        rcases hF with ⟨p, arc, hp, hEdge, hCross⟩
        refine ⟨p, arc, hp, ?_, ?_⟩
        · intro u v huv hadj
          exact hEdge u v huv (hGF hadj)
        · intro u v x y huv hxy hadj hadj' hne t ht s hs hEq
          exact hCross u v x y huv hxy (hGF hadj) (hGF hadj') hne t ht s hs hEq)
      H hH
  exact ⟨K, hHK, hK, hcard, fun L hKL hL => hmax L hKL hL⟩