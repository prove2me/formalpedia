-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_of_adj_imp_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:59:59.071087+00:00
-- url     : https://prove2.me/submissions/9f3d1cb4-4aaa-4300-b1a1-dd582051de38

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (N M : SimpleGraph V)
    (hsub : ∀ u v, N.Adj u v → M.Adj u v) :
    N.edgeSet.ncard ≤ M.edgeSet.ncard := by
  have hNM : N ≤ M := by
    intro u v huv
    exact hsub u v huv
  exact Set.ncard_le_ncard ((SimpleGraph.edgeSet_subset_edgeSet).2 hNM)