-- Prove2me | solution 1 for WilliamsonShmoys.unreachable_pair_of_disconnected__p2m_353b61e0_8cec_4373_8be0_6e3443fc0711_a4
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:40:18.999415+00:00
-- url     : https://prove2.me/submissions/359e5084-f38e-4d5f-bd23-f86dc3df3579

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hdisc : ¬ H.Connected) :
    ∃ u v : V, ¬ Relation.ReflTransGen H.Adj u v := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  rw [SimpleGraph.connected_iff_exists_forall_reachable] at hdisc
  simp only [not_exists, not_forall, not_not] at hdisc
  obtain ⟨u⟩ := (inferInstance : Nonempty V)
  obtain ⟨v, hv⟩ := hdisc u
  refine ⟨u, v, ?_⟩
  simpa only [SimpleGraph.reachable_eq_reflTransGen] using hv
