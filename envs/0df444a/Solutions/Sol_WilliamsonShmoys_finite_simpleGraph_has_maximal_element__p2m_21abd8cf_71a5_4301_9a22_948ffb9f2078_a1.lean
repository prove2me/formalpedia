-- Prove2me | solution 1 for WilliamsonShmoys.finite_simpleGraph_has_maximal_element__p2m_21abd8cf_71a5_4301_9a22_948ffb9f2078_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:52:59.772866+00:00
-- url     : https://prove2.me/submissions/6dbd8c68-ba41-4414-8654-caa4147d9bd0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hP : ∃ K : SimpleGraph V, P K) :
    ∃ K : SimpleGraph V, P K ∧
      ∀ L : SimpleGraph V, P L → K ≤ L → L ≤ K := by
  classical
  obtain ⟨G, hG⟩ := hP
  obtain ⟨K, hGK, hmax⟩ := Finite.exists_le_maximal hG
  refine ⟨K, (maximal_iff.mp hmax).1, ?_⟩
  intro L hL hKL
  have hEq : K = L := Maximal.eq_of_le hmax hL hKL
  exact hEq.symm.le