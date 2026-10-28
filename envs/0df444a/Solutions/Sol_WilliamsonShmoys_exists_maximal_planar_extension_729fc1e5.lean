-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension_729fc1e5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:13:57.099875+00:00
-- url     : https://prove2.me/submissions/97f4e13b-645f-4406-9539-6e42ae3df01a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V, Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      ∀ S : SimpleGraph V, R ≤ S →
        WilliamsonShmoys.HasPlanarDrawingOn S → S = R := by
  classical
  let P : Set (SimpleGraph V) :=
    {R | Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R}
  have hPfin : P.Finite := Set.toFinite P
  have hPne : P.Nonempty := ⟨Q, le_rfl, hQ⟩
  obtain ⟨R, hR⟩ := hPfin.exists_maximal hPne
  refine ⟨R, hR.1.1, hR.1.2, ?_⟩
  intro S hRS hS
  have hQS : Q ≤ S := hR.1.1.trans hRS
  have hSmem : S ∈ P := ⟨hQS, hS⟩
  have hSR : S ≤ R := hR.2 hSmem hRS
  exact le_antisymm hSR hRS