-- Prove2me | solution 1 for WilliamsonShmoys.planarAugmentation_edgeCount__p2m_6ad3e488_df98_4029_b402_def6549b4337_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:31:57.542256+00:00
-- url     : https://prove2.me/submissions/fa07efcb-ec59-4d14-889c-81d38cdfc15c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximalPlanarSupergraph__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
import Theorems.Thm_WilliamsonShmoys_maximalPlanar_edgeCount__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      HasPlanarDrawingOn L ∧
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel L.Adj := dL
       K.edgeFinset ⊆ L.edgeFinset) ∧
      (letI : DecidableRel L.Adj := dL
       L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨L, dL, hL, hKL, hmax⟩ :=
    WilliamsonShmoys.exists_maximalPlanarSupergraph__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
      K dK hK
  refine ⟨L, dL, hL, hKL, ?_⟩
  exact WilliamsonShmoys.maximalPlanar_edgeCount__p2m_a840099d_4605_4d5d_aa63_effaab21667c_a1
    L dL hL hmax hn