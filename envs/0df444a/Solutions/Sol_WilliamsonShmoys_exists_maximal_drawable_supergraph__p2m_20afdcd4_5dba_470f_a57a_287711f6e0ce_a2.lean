-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:46:42.433129+00:00
-- url     : https://prove2.me/submissions/711b00f1-fa6e-4bf0-8a62-e5539f68e24f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      WilliamsonShmoys.HasPlanarDrawingOn M /\ L <= M /\
        (forall N : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn N -> M <= N -> N = M) := by
  obtain ⟨M, hLM, hMm⟩ := Finite.exists_le_maximal (p := WilliamsonShmoys.HasPlanarDrawingOn) hL
  exact ⟨M, hMm.prop, hLM, fun N hN hMN => le_antisymm (hMm.2 hN hMN) hMN⟩
