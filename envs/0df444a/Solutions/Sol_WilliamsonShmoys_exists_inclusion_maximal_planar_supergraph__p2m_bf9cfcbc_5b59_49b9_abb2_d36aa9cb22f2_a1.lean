-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:53:33.635185+00:00
-- url     : https://prove2.me/submissions/bc903c05-ad80-42d0-80b4-e1e305a1cce8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_preorder_maximal_extension__p2m_8fa7b5e9_9ae2_4561_bc62_ceb5c7ac1a09_a1
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    Exists fun H : SimpleGraph V =>
      And (M <= H) (And (HasPlanarDrawingOn H)
        (forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K <= H)) := by
  exact WilliamsonShmoys.finite_preorder_maximal_extension__p2m_8fa7b5e9_9ae2_4561_bc62_ceb5c7ac1a09_a1
    (P := HasPlanarDrawingOn) M hM