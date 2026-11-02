-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6e84ab66_a241_4b3a_ab2e_bd91b32f8011_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:38:15.166758+00:00
-- url     : https://prove2.me/submissions/c2c3705b-1963-4b8f-9972-31133a949b4d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate__p2m_7202bf9d_a814_4b20_b0a7_1713c12fe256_a1
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ H.Connected ∧
      (∀ K : SimpleGraph V, HasPlanarDrawingOn K → H ≤ K → K ≤ H) := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_7202bf9d_a814_4b20_b0a7_1713c12fe256_a1
      HasPlanarDrawingOn G hG
  refine ⟨H, hGH, hH, hconn.mono hGH, ?_⟩
  intro K hK hHK
  exact hMax K hK hHK