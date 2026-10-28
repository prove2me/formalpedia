-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_maximal_extension_v2_aux
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:17:26.285663+00:00
-- url     : https://prove2.me/submissions/80c01a64-11f3-474c-ac3e-a72c969950a5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      (∀ {u v}, U.Adj u v → W.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      (∀ (X : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn X →
        (∀ {u v}, W.Adj u v → X.Adj u v) → X = W) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => U ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : U ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, fun h => hPQ h, hQ, fun R hR hQR' => ?_⟩
  have hQR : Q ≤ R := fun _ _ h => hQR' h
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
