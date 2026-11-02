-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximalPlanar_augmentDisconnected__p2m_b38e7e0d_55b6_4800_9dde_424996f32dbe_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T02:28:31.594204+00:00
-- url     : https://prove2.me/submissions/afe51b1e-f999-45a1-8b63-ac42577d69c2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_of_disconnected

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V)
    (hdisc : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hKH, hH, hneq⟩ :=
    WilliamsonShmoys.planar_augmentation_of_disconnected K hK hn hdisc
  refine ⟨H, hKH, ?_, hH⟩
  intro hHK
  exact hneq hHK.symm