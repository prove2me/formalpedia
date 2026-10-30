-- Prove2me | solution 1 for WilliamsonShmoys.exists_ordered_nonadjacent_unreachable_pair__p2m_6a622dd5_43ee_4f6f_8030_5cf16ee40909_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:54.33662+00:00
-- url     : https://prove2.me/submissions/bc41f79e-1967-4b18-b984-b27d366fcb6f

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 0 < Fintype.card V) (hDisconnected : ¬ H.Connected) : ∃ u v : V, u < v ∧ ¬ H.Adj u v ∧ ¬ H.Reachable u v := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp hV
  have hpre : ¬ H.Preconnected := by
    intro hconn
    letI : Nonempty V := hne
    exact hDisconnected (SimpleGraph.Connected.mk hconn)
  have hnotpre : ¬ ∀ u v : V, H.Reachable u v := hpre
  push_neg at hnotpre
  obtain ⟨u, v, huv⟩ := hnotpre
  have hneq : u ≠ v := by
    intro heq
    apply huv
    simpa [heq] using (SimpleGraph.Reachable.rfl (G := H) (u := u))
  have hnotvu : ¬ H.Reachable v u := by
    intro hvu
    exact huv (SimpleGraph.Reachable.symm hvu)
  rcases lt_or_gt_of_ne hneq with huvlt | hvult
  · refine ⟨u, v, huvlt, ?_, huv⟩
    intro hadj
    exact huv hadj.reachable
  · refine ⟨v, u, hvult, ?_, hnotvu⟩
    intro hadj
    exact hnotvu hadj.reachable