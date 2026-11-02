-- Prove2me | solution 1 for WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_a21b9daf_96c0_42bf_b053_e1966758807a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:11:59.237377+00:00
-- url     : https://prove2.me/submissions/e17ec86f-7b92-48a1-ae41-bbdd81350b4e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ K : SimpleGraph V,
          H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by
  classical
  let p : SimpleGraph V → Prop :=
    fun H => G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H
  obtain ⟨H, hdec, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 ⟨G, le_rfl, hdraw⟩
  letI : DecidableRel H.Adj := hdec
  refine ⟨H, hExt.prop.1, hExt.prop.2, ?_⟩
  intro K hHK hK
  have hEq : H = K :=
    (hExt.le_iff_eq ⟨hExt.prop.1.trans hHK, hK⟩).mp hHK
  exact le_of_eq hEq.symm