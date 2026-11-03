-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_maximal_extension__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:19:38.618785+00:00
-- url     : https://prove2.me/submissions/d0076df4-e2a0-4a5e-9c90-1cb847ff87a4

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_finite_choice__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (T : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hT : P T)
    (hmono : ∀ G H : SimpleGraph V, G ≤ H → P G → P H) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧ P U ∧
        ∀ W : SimpleGraph V, U ≤ W → P W → W = U :=
  WilliamsonShmoys.planar_drawing_maximal_extension_finite_choice__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a2 T P hT