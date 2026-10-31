-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_strict_extension_below_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:20:17.255346+00:00
-- url     : https://prove2.me/submissions/3e36460d-eccc-4327-88ec-eee3b3a6ac97

import Theorems.Thm_WilliamsonShmoys_planar_strict_edge_augmentation__p2m_97e2a771_8b9b_4035_b979_2c6a9ee02dac_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V)
    (hSmall : N.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ P : SimpleGraph V, N <= P ∧ P ≠ N ∧ HasPlanarDrawingOn P :=
  WilliamsonShmoys.planar_strict_edge_augmentation__p2m_97e2a771_8b9b_4035_b979_2c6a9ee02dac_a1 N hN hCard hSmall
