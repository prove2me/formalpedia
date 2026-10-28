-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_density
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:36:48.701978+00:00
-- url     : https://prove2.me/submissions/b8fae644-9c85-4be5-acc9-a14de34f6047
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_8b6262cf
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_density_8b6262cf

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_8b6262cf K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_extension_density_8b6262cf L hL hV hmax⟩