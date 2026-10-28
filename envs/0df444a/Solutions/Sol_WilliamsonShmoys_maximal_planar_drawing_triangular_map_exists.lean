-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_triangular_map_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T22:59:04.201161+00:00
-- url     : https://prove2.me/submissions/08af2fe1-4d76-458e-9f22-bbaddb7f517a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_has_triangular_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    ∃ (m : Nat), Nonempty (WilliamsonShmoys.TriangularMap H (Fin m)) := by
  classical
  obtain ⟨K, hHK, hK, m, hMap⟩ :=
    WilliamsonShmoys.planar_drawing_on_has_triangular_completion H hH hV
  have hKH : K ≤ H := hMax K hHK hK
  have hEq : K = H := le_antisymm hKH hHK
  subst K
  exact ⟨m, hMap⟩