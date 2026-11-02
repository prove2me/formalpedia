-- Prove2me | solution 1 for WilliamsonShmoys.exists_card_maximal_planar_extension__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:37:55.123105+00:00
-- url     : https://prove2.me/submissions/c37308c6-1798-424f-bb46-27a8eb91124a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2
import Theorems.Thm_finite_maximum_on_nonempty_predicate__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  letI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simpleGraph__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let P : SimpleGraph V → Prop := fun G => N ≤ G ∧ HasPlanarDrawingOn G
  obtain ⟨K, hK, hmax⟩ :=
    finite_maximum_on_nonempty_predicate__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2
      (α := SimpleGraph V) P (fun G => G.edgeSet.ncard)
      ⟨N, le_rfl, hN⟩
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hKL hL
  exact hmax L ⟨le_trans hK.1 hKL, hL⟩