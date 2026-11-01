-- Prove2me | solution 1 for WilliamsonShmoys.connected_extension_has_new_edge__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:13:41.864597+00:00
-- url     : https://prove2.me/submissions/9b46898e-fa59-4e35-a18e-8bd8d495de36

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K M : SimpleGraph V)
    (hKM : K ≤ M)
    (hK : ¬ K.Connected)
    (hM : M.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Adj u v ∧ M.Adj u v := by
  by_contra hnew
  apply hK
  apply hM.mono
  intro u v huv
  by_contra hnotK
  exact hnew ⟨u, v, huv.ne, hnotK, huv⟩