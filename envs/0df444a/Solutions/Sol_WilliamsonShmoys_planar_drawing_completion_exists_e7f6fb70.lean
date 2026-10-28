-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_exists_e7f6fb70
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:13:32.244205+00:00
-- url     : https://prove2.me/submissions/de3a2169-7dc9-43f4-a5ac-b3a6ddf1c0db

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, Y.Adj u v → H.Adj u v) ∧
      Y.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        ∀ ⦃u v⦄, K.Adj u v → H.Adj u v) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => Y ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hY⟩⟩
  obtain ⟨hPQ, hQ⟩ : Y ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have key : ∀ R : SimpleGraph V, Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by
    intro R hQR hR
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  refine ⟨Q, fun u v h => hPQ h, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hPQ) (Set.toFinite _), hQ, ?_⟩
  intro K hK hKd u v huv
  have := key K (fun a b h => hK h) hKd
  subst this; exact huv
