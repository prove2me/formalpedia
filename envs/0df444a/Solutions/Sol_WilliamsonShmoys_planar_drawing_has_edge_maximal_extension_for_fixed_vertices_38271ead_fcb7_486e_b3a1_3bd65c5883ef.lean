-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_edge_maximal_extension_for_fixed_vertices_38271ead_fcb7_486e_b3a1_3bd65c5883ef
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:15:13.970659+00:00
-- url     : https://prove2.me/submissions/220e671e-1a0e-4d9a-97ac-36601b250a8e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V,
        M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ M := by
  let P : SimpleGraph V → Prop := WilliamsonShmoys.HasPlanarDrawingOn
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => H ≤ X0 ∧ P X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hH⟩⟩
  obtain ⟨hPQ, hQ⟩ : H ≤ Q ∧ P Q := (Finset.mem_filter.mp hQm).2
  have key : ∀ R : SimpleGraph V, Q ≤ R → P R → R = Q := by
    intro R hQR hR
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact ⟨Q, hPQ, hQ, fun W h1 h2 => (key W h1 h2).le⟩
