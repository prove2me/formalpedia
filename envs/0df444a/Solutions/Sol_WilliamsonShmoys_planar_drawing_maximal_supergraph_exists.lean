-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_exists
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:21:57.044864+00:00
-- url     : https://prove2.me/submissions/dddfade1-83be-485f-8061-0715741ce2c1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V,
      LE.le Z W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V,
        LE.le W X → WilliamsonShmoys.HasPlanarDrawingOn X → LE.le X W := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun W => LE.le Z W ∧ WilliamsonShmoys.HasPlanarDrawingOn W)
  have hne : candidates.Nonempty := by
    refine ⟨Z, ?_⟩
    simp [candidates, hZ]
  obtain ⟨W, hW⟩ := candidates.exists_maximal hne
  have hWprop : LE.le Z W ∧ WilliamsonShmoys.HasPlanarDrawingOn W := by
    simpa [candidates] using hW.1
  refine ⟨W, hWprop.1, hWprop.2, ?_⟩
  intro X hWX hX
  have hXmem : X ∈ candidates := by
    simp [candidates, hWprop.1.trans hWX, hX]
  exact hW.2 hXmem hWX