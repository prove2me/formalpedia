-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_on_fixed_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:41:53.969707+00:00
-- url     : https://prove2.me/submissions/188ef788-374d-430d-b908-224eb6b12d7e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = W := by
  classical
  let S : Set (SimpleGraph V) :=
    {G | U ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨U, le_rfl, hU⟩
  obtain ⟨W, hWmem, hWmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨W, hWmem.1, hWmem.2, ?_⟩
  intro X hWX hX
  have hXmem : X ∈ S := ⟨hWmem.1.trans hWX, hX⟩
  have hXW : X ≤ W := hWmax hXmem hWX
  exact le_antisymm hXW hWX