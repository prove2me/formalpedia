-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_261600ee_7fa4_4a45_a37b_002442c9d475_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:35:56.4072+00:00
-- url     : https://prove2.me/submissions/1a889488-27c5-4aaf-9373-38685622932d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_property_supergraph__p2m_8cd0804a_f792_4057_bb92_319536b24856_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by
  exact WilliamsonShmoys.exists_inclusion_maximal_property_supergraph__p2m_8cd0804a_f792_4057_bb92_319536b24856_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) G hG