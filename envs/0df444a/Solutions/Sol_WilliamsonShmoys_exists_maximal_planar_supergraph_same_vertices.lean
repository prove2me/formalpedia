-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:14:50.642998+00:00
-- url     : https://prove2.me/submissions/c93cb3c1-e5f2-46bc-a086-a0a2c53b2415

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      S ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by
  classical
  let P : Set (SimpleGraph V) :=
    {T | S ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T}
  have hPfinite : P.Finite := Set.toFinite P
  have hPnonempty : P.Nonempty := ⟨S, le_rfl, hS⟩
  obtain ⟨T, hTmax⟩ := hPfinite.exists_maximal hPnonempty
  refine ⟨T, hTmax.1.1, hTmax.1.2, ?_⟩
  intro U hTU hU
  have hUmem : U ∈ P := ⟨hTmax.1.1.trans hTU, hU⟩
  exact ((maximal_iff.mp hTmax).2 hUmem hTU).symm