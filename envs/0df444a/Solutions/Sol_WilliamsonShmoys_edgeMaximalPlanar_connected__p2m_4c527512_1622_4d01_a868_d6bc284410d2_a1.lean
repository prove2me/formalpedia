-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximalPlanar_connected__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:57:34.026938+00:00
-- url     : https://prove2.me/submissions/fe284d49-fadb-4695-b36a-f6b9aba9ee63

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_augmentDisconnected__p2m_b38e7e0d_55b6_4800_9dde_424996f32dbe_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H = K)
    (hn : 3 ≤ Fintype.card V) :
    K.Connected := by
  by_contra hconn
  obtain ⟨H, hle, hne, hH⟩ :=
    WilliamsonShmoys.edgeMaximalPlanar_augmentDisconnected__p2m_b38e7e0d_55b6_4800_9dde_424996f32dbe_a2
      K hK hn hconn
  have heq : H = K := hmax H hle hH
  exact hne heq