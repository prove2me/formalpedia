-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_step_closes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:33:07.155006+00:00
-- url     : https://prove2.me/submissions/d4f0f3f8-6bbf-4b08-8a47-7f17937fcfc7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hStep : ∀ (K : SimpleGraph V), G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ H : SimpleGraph V,
        K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∃ u v : V, ¬ K.Reachable u v ∧ H.Adj u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V =>
      G ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hG⟩⟩
  obtain ⟨hGQ, hQ⟩ : G ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hGQ, hQ, ?_⟩
  by_contra hc
  obtain ⟨H, hQH, hH, u, v, huv, hadj⟩ := hStep Q hGQ hQ hc
  have hne : Q ≠ H := by
    rintro rfl; exact huv hadj.reachable
  have hlt : Q < H := lt_of_le_of_ne hQH hne
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax H (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGQ.trans hQH, hH⟩)
  omega
