-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_e6f2f448_1eb8_42c3_a63b_d113f4e2074c_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:42:24.223873+00:00
-- url     : https://prove2.me/submissions/12696279-05ed-479e-a553-1d57fd2033db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_drawable_triangulation_extension__p2m_126577ef_f856_473b_b1f2_d55f4854fb26_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj
     K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.exists_drawable_triangulation_extension__p2m_126577ef_f856_473b_b1f2_d55f4854fb26_a1
      K hcard hK
  have hLK : L = K := hmax L hKL hL
  subst L
  exact hcount