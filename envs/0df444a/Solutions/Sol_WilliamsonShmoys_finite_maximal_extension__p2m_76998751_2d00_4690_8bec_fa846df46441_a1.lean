-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_76998751_2d00_4690_8bec_fa846df46441_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:56:47.669507+00:00
-- url     : https://prove2.me/submissions/0b496eac-7185-4ddc-a1b5-9acd05a9035b

import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (Y : SimpleGraph V) (hY : P Y) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧ P Z ∧
      ∀ W : SimpleGraph V, Z ≤ W → P W → W ≤ Z :=
  WilliamsonShmoys.exists_maximal_supergraph_for_predicate P Y hY
