-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:53:37.787574+00:00
-- url     : https://prove2.me/submissions/de392961-e4f6-4caf-8090-00b30947747d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_344124b5_d420_40df_b6d0_816baecb63ba_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_344124b5_d420_40df_b6d0_816baecb63ba_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    (∀ K : SimpleGraph V,
      H.edgeFinset ⊆ K.edgeFinset →
      HasPlanarDrawingOn K →
      K.edgeFinset ⊆ H.edgeFinset) →
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  intro hmax
  have hu := WilliamsonShmoys.planar_edge_upper_bound__p2m_344124b5_d420_40df_b6d0_816baecb63ba_a2 H hH hcard
  have hl := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_344124b5_d420_40df_b6d0_816baecb63ba_a2 H hH hcard hmax
  omega