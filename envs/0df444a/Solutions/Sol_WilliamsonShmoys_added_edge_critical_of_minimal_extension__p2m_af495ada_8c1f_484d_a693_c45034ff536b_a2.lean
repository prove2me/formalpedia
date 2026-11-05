-- Prove2me | solution 1 for WilliamsonShmoys.added_edge_critical_of_minimal_extension__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:20:24.090525+00:00
-- url     : https://prove2.me/submissions/58ea37b3-977c-4f5d-b96b-84fcb9350eb4

import Mathlib

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M H : SimpleGraph V)
    (hMH : M ≤ H) (hconn : H.Connected)
    (hmin : ∀ K : SimpleGraph V, M ≤ K → K ≤ H → K.Connected → K = H) :
    ∀ u v : V, H.Adj u v → ¬ M.Adj u v →
      ¬ (H.deleteEdges {s(u, v)}).Reachable u v := by
  classical
  intro u v huv hMnuv hreach
  let K : SimpleGraph V := H.deleteEdges ({s(u, v)} : Set (Sym2 V))
  have hnotBridge : ¬ H.IsBridge s(u, v) := by
    intro hb
    exact (SimpleGraph.isBridge_iff.mp hb) hreach
  have hKconn : K.Connected := by
    simpa [K] using hconn.connected_delete_edge_of_not_isBridge hnotBridge
  have hK'H : K ⊔ M ≤ H := by
    refine sup_le ?_ hMH
    simpa [K] using
      (SimpleGraph.deleteEdges_le (G := H) (s := ({s(u, v)} : Set (Sym2 V))))
  have hK'conn : (K ⊔ M).Connected :=
    SimpleGraph.Connected.mono le_sup_left hKconn
  have hEq : K ⊔ M = H := hmin (K ⊔ M) le_sup_right hK'H hK'conn
  have hnot : ¬ (K ⊔ M).Adj u v := by
    rw [SimpleGraph.sup_adj]
    rintro (hKuv | hMuv)
    · simpa [K] using hKuv
    · exact hMnuv hMuv
  exact hnot (by simpa [hEq] using huv)
