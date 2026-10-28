-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_drawing_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:36:35.691541+00:00
-- url     : https://prove2.me/submissions/6d19d34a-42e1-4257-84f3-f4cb8e86351c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hconn : Q.Connected) :
    ∃ M : SimpleGraph V,
      Q ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ R : SimpleGraph V,
        M ≤ R →
        WilliamsonShmoys.HasPlanarDrawingOn R →
        R ≤ M := by
  classical
  obtain ⟨A, hAm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => Q ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨Q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hQ⟩⟩
  obtain ⟨hPA, hA⟩ : Q ≤ A ∧ WilliamsonShmoys.HasPlanarDrawingOn A := (Finset.mem_filter.mp hAm).2
  refine ⟨A, hPA, hA, fun R hAR hR => ?_⟩
  have hEq : R = A := by
    by_contra hne
    have hlt : A < R := lt_of_le_of_ne hAR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPA.trans hAR, hR⟩)
    omega
  exact hEq.le
