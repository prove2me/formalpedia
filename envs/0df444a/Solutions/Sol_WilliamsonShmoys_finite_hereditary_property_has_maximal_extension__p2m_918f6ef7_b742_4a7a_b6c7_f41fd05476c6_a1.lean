-- Prove2me | solution 1 for WilliamsonShmoys.finite_hereditary_property_has_maximal_extension__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:45:31.182037+00:00
-- url     : https://prove2.me/submissions/5e6c5906-8fad-42de-ab0e-0fdcc53efc9e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K)
    (hmono : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G) :
    ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧
      ∀ M : SimpleGraph V, L ≤ M → P M → M = L := by
  classical
  obtain ⟨L, hKL, hmax⟩ := Finite.exists_le_maximal hK
  refine ⟨L, hKL, hmax.prop, ?_⟩
  intro M hLM hPM
  by_contra hne
  apply hmax.not_prop_of_gt (lt_of_le_of_ne hLM (Ne.symm hne)) hPM