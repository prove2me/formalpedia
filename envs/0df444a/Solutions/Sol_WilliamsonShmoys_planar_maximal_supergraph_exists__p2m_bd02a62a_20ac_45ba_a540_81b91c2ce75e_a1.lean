-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_bd02a62a_20ac_45ba_a540_81b91c2ce75e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:48.010282+00:00
-- url     : https://prove2.me/submissions/ad8b2fd6-c49e-48e4-8eb9-49cea47ec092

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_poset_maximal_extension__p2m_bd9d7987_6824_4383_ac2f_f887fa429ccf_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V)
    (hConn : K.Connected) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    finite_poset_maximal_extension__p2m_bd9d7987_6824_4383_ac2f_f887fa429ccf_a1
      (α := SimpleGraph V) (P := HasPlanarDrawingOn) K hK
  exact ⟨H, hKH, hH, hmax⟩