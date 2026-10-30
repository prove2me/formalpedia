-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_7871e1d9_1c06_462f_bc77_343c5987d399_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:50:35.2674+00:00
-- url     : https://prove2.me/submissions/aa31e65c-bed0-43c8-847c-81b12c3f7124

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_finite_simpleGraph__p2m_c6944f63_e851_4122_bc82_20fe0d441b4b_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ H : SimpleGraph V, M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = M := by
  classical
  exact WilliamsonShmoys.exists_maximal_extension_finite_simpleGraph__p2m_c6944f63_e851_4122_bc82_20fe0d441b4b_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) G hDraw