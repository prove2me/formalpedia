-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:31:31.504142+00:00
-- url     : https://prove2.me/submissions/60b69691-e45e-4ed0-9bea-1a2bceadab02

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_property_supergraph__p2m_bde7bab7_9900_4674_96b7_2eea7887c7cc_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hconn : N.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v : V, N.Adj u v → H.Adj u v) ∧
      HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ u v : V, H.Adj u v → K.Adj u v) →
        HasPlanarDrawingOn K → K = H) := by
  obtain ⟨H, hNH, hH, hmax⟩ :=
    exists_maximal_property_supergraph__p2m_bde7bab7_9900_4674_96b7_2eea7887c7cc_a1
      HasPlanarDrawingOn N hN
  refine ⟨H, hNH, hH, ?_⟩
  intro K hHK hK
  apply hmax K ?_ hK hHK
  intro u v huv
  exact hHK u v (hNH u v huv)