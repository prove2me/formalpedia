-- Prove2me | solution 1 for WilliamsonShmoys.exists_minimal_connected_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:04:49.321977+00:00
-- url     : https://prove2.me/submissions/a69493fc-174b-4e9d-ba6b-de9de0536617
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_minimal_connected_supergraph__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2
import Theorems.Thm_WilliamsonShmoys_added_edge_critical_of_minimal_extension__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) :
    ∃ H : SimpleGraph V, M ≤ H ∧ H.Connected ∧
      ∀ u v : V, H.Adj u v → ¬ M.Adj u v →
        ¬ (H.deleteEdges {s(u, v)}).Reachable u v := by
  obtain ⟨H, hMH, hconn, hmin⟩ :=
    WilliamsonShmoys.exists_minimal_connected_supergraph__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2 M
  refine ⟨H, hMH, hconn, ?_⟩
  exact WilliamsonShmoys.added_edge_critical_of_minimal_extension__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2
    M H hMH hconn hmin