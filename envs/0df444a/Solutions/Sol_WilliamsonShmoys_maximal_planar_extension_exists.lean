-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:51:19.994304+00:00
-- url     : https://prove2.me/submissions/59a8ea18-1bdb-4a48-a418-e4192a8f54d9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ ⦃u v⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        ∀ ⦃u v⦄, L.Adj u v → K.Adj u v) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => H ≤ G ∧ HasPlanarDrawingOn G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hH⟩⟩
  obtain ⟨hPQ, hQ⟩ : H ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, fun u v h => hPQ h, hQ, fun R hQR' hR => ?_⟩
  have hQR : Q ≤ R := fun u v h => hQR' h
  suffices R ≤ Q from fun u v h => this h
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (fun h => hne (h ▸ le_rfl))
  have h1 : Q.edgeFinset ⊂ R.edgeFinset := SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
  have h2 := Finset.card_lt_card h1
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
