-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximizer_exists_7f31c9a2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:47:41.531674+00:00
-- url     : https://prove2.me/submissions/3d18de9e-cced-40c7-b48f-08907f303806

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      (∀ u v, K.Adj u v → H.Adj u v) ∧
      HasPlanarDrawingOn H ∧
      ∀ G : SimpleGraph V,
        (∀ u v, K.Adj u v → G.Adj u v) →
        HasPlanarDrawingOn G →
        G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => K ≤ X0 ∧ HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hDraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : K ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have hc : ∀ X : SimpleGraph V, X.edgeSet.ncard = X.edgeFinset.card := fun X => by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  refine ⟨Q, fun u v h => hPQ h, hQ, ?_⟩
  intro W hKW hW
  rw [hc, hc]
  exact hmax W (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u v h => hKW u v h, hW⟩)
