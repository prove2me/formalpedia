-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_aa8c3543_6a70_4578_ab0d_df04a85e5168_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:52:32.307412+00:00
-- url     : https://prove2.me/submissions/634d63f6-dd39-4228-bd8e-c945de3e18fd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_26140903_fcb8_4c7c_a0cc_72edca446c76_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hR : HasPlanarDrawingOn R)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V, R ≤ S ∧ HasPlanarDrawingOn S ∧
      ∀ [hSdec : DecidableRel S.Adj], S.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨S, hRS, hS, hc⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_26140903_fcb8_4c7c_a0cc_72edca446c76_a1 R hR hcard
  refine ⟨S, hRS, hS, ?_⟩
  intro hSdec
  rw [← S.coe_edgeFinset, Set.ncard_coe_finset] at hc
  exact hc
