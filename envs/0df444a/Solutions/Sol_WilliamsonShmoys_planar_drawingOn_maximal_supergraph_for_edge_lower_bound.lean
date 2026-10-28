-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_maximal_supergraph_for_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:13:08.5881+00:00
-- url     : https://prove2.me/submissions/53de87bc-395a-4070-ba6a-371bfed3d228

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      (∀ u v, T.Adj u v → U.Adj u v) ∧
      (∀ W : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn W →
        (∀ u v, U.Adj u v → W.Adj u v) →
        ∀ u v, W.Adj u v → U.Adj u v) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => T ≤ H ∧ HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hT⟩⟩
  obtain ⟨hPQ, hQ⟩ : T ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hQ, fun u v h => hPQ h, fun R hR hQR' => ?_⟩
  have hQR : Q ≤ R := fun u v h => hQR' u v h
  have heq : R = Q := by
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  subst heq
  exact fun u v h => h
