-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_lower_bound__p2m_8514b45e_f592_4fc5_88fb_d0f4ef7fe022_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:15:35.233445+00:00
-- url     : https://prove2.me/submissions/cf905a81-10f5-4aed-a78d-62bf60528b47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_b554ef36_a96a_42de_b297_4474260662ac_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    3 * Fintype.card V ≤ H.edgeFinset.card + 6 := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨K, hsub, hK, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_b554ef36_a96a_42de_b297_4474260662ac_a1 H hH hcard
  have hEq : K = H := hmax K (by intro u v huv; exact hsub huv) hK
  subst K
  omega