-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_connected__p2m_8955ab15_7b83_4a31_a256_432a7dfdfb1c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:29.656467+00:00
-- url     : https://prove2.me/submissions/d63006d9-1174-44a1-8487-08f901f25bee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_of_not_connected__p2m_c0200a01_8eb0_4c56_8f2c_cdc0d10e5a12_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hU : HasPlanarDrawingOn U)
    (hUmax : ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W = U) :
    U.Connected := by
  by_contra hdisc
  obtain ⟨a, b, W, hab, hnot, hle, hne, hWab, hW⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_of_not_connected__p2m_c0200a01_8eb0_4c56_8f2c_cdc0d10e5a12_a1
      U hV hU hdisc
  have heq : W = U := hUmax W hle hW
  exact hne heq
