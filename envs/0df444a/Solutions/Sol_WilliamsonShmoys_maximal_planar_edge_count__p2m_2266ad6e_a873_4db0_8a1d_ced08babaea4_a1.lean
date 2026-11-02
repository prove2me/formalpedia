-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_2266ad6e_a873_4db0_8a1d_ced08babaea4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:05:18.108846+00:00
-- url     : https://prove2.me/submissions/d4929d03-e0be-46a5-9056-0975273d52de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion__p2m_31190146_93e5_4043_a404_538cf81f5878_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn L)
    (hmax : ∀ K : SimpleGraph V, L.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K → K.edgeSet = L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hsub, hK, hcount⟩ :=
    WilliamsonShmoys.planar_completion__p2m_31190146_93e5_4043_a404_538cf81f5878_a1
      L hcard hplanar
  have heq : K.edgeSet = L.edgeSet := hmax K hsub hK
  rw [heq] at hcount
  exact hcount