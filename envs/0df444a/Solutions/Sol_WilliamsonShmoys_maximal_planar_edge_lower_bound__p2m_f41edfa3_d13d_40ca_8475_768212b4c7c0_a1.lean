-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f41edfa3_d13d_40ca_8475_768212b4c7c0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:07:15.491521+00:00
-- url     : https://prove2.me/submissions/3d1f3d51-588b-4801-add5-7ef6d1ddd238
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_4a0e4ba9_45c9_4065_a5b6_23412bcd7af0_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      3 * Fintype.card V ≤ K.edgeFinset.card + 6) := by
  rcases WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_4a0e4ba9_45c9_4065_a5b6_23412bcd7af0_a1
      K hV hK with ⟨L, hKL, hL, hcount⟩
  have hLK : L ≤ K := hmax L hKL hL
  have hEq : K = L := le_antisymm hKL hLK
  subst L
  omega