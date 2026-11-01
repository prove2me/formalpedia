-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_extension_has_connected_member__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:38:03.730602+00:00
-- url     : https://prove2.me/submissions/213c7f5f-b6ef-4ba1-a1c7-f2d1f70acb77

import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_graph_extension_has_maximal_member__p2m_6589fa02_37e2_48f2_abf0_d80cd3574afc_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H)
    (hstep : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ G' : SimpleGraph V, G < G' ∧ P G') :
    ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ P G := by
  obtain ⟨M, hHM, hPM, hmax⟩ :=
    WilliamsonShmoys.finite_graph_extension_has_maximal_member__p2m_6589fa02_37e2_48f2_abf0_d80cd3574afc_a1
      H P hP
  by_cases hconn : M.Connected
  · exact ⟨M, hHM, hconn, hPM⟩
  · obtain ⟨M', hMM', hPM'⟩ := hstep M hPM hconn
    exact False.elim (hmax M' hMM' hPM')