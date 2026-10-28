-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exists_for_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:34:02.690307+00:00
-- url     : https://prove2.me/submissions/7622436c-7c11-4351-b576-4bd9dfb7ba95

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      (∀ {u v}, S.Adj u v → T.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      (∀ U : SimpleGraph V,
        (∀ {u v}, T.Adj u v → U.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn U →
        ∀ {u v}, U.Adj u v → T.Adj u v) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => S ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : S ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, fun h => hPQ h, hQ, fun R hQR' hR => ?_⟩
  have hQR : Q ≤ R := fun _ _ h => hQR' h
  have hEq : R = Q := by
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  intro u v h
  rw [hEq] at h
  exact h
