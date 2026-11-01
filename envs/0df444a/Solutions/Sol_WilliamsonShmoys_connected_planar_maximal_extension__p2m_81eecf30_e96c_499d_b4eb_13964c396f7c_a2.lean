-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_maximal_extension__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:14:19.977034+00:00
-- url     : https://prove2.me/submissions/bac4127d-e71d-49d0-989d-0b94c2fa462c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_subgraph__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_of_downward_closed__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (C : SimpleGraph V) (hC : WilliamsonShmoys.HasPlanarDrawingOn C)
    (hconn : C.Connected) :
    ∃ H : SimpleGraph V,
      C ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        (letI : DecidableRel K.Adj := Classical.decRel _;
         H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by
  let P : SimpleGraph V → Prop := WilliamsonShmoys.HasPlanarDrawingOn
  have hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G := by
    intro G H hGH hH
    exact WilliamsonShmoys.planar_drawing_on_subgraph__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1 hGH hH
  obtain ⟨H, hCH, hPH, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_extension_of_downward_closed__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1
      P hdown C hC
  refine ⟨H, hCH, hconn.mono hCH, hPH, ?_⟩
  intro K
  letI : DecidableRel K.Adj := Classical.decRel _
  intro hHK hK
  exact hmax K hHK hK