-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_b9846791_42e7_44fd_ba07_2c181cf57015_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:06:35.957191+00:00
-- url     : https://prove2.me/submissions/80aad8b6-1851-45c5-a690-f8ebf97fae09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_augmentation__p2m_89d85e84_1aea_42cb_ac41_e0b11d6aa537_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N -> HasPlanarDrawingOn N -> N = M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     3 * Fintype.card V <= M.edgeFinset.card + 6) := by
  classical
  obtain ⟨N, hMN, hN, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_augmentation__p2m_89d85e84_1aea_42cb_ac41_e0b11d6aa537_a1
      M hV hM
  have hNM : N = M := hmax N hMN hN
  subst N
  exact le_of_eq hcard