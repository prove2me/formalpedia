-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_connected_extension_of_local_step__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:10:32.691703+00:00
-- url     : https://prove2.me/submissions/15a5ced1-de12-44c4-b0ca-a79b0bc5ea73

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1
import Theorems.Thm_WilliamsonShmoys_connected_of_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (step : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) :
    ∀ (G : SimpleGraph V), P G →
      ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ P H := by
  intro G hG
  obtain ⟨H, hGH, hPH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1
      P G hG
  refine ⟨H, hGH, ?_, hPH⟩
  exact WilliamsonShmoys.connected_of_maximal_invariant_extension__p2m_ae139772_cde8_4644_bb54_63943db19887_a1
    P step H hPH hmax