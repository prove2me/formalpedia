-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_extension_has_maximal_member__p2m_6589fa02_37e2_48f2_abf0_d80cd3574afc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:40:54.056568+00:00
-- url     : https://prove2.me/submissions/f696faa1-dc02-4293-8878-be3b1df053f3

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H) :
    ∃ M : SimpleGraph V, H ≤ M ∧ P M ∧
      ∀ G' : SimpleGraph V, M < G' → ¬ P G' := by
  classical
  obtain ⟨M, hHM, hmax⟩ := Finite.exists_le_maximal (p := P) hP
  exact ⟨M, hHM, hmax.prop, fun G' hMG' => hmax.not_prop_of_gt hMG'⟩