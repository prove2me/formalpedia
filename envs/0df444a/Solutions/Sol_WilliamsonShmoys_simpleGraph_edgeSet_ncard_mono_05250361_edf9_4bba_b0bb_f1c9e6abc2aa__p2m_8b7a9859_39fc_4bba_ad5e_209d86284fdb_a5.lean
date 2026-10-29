-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:26:20.177675+00:00
-- url     : https://prove2.me/submissions/da5f84e1-596f-4db8-b6cd-b6f7b00bffa7

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (M Q : SimpleGraph V)
    (hMQ : ∀ {u v : V}, M.Adj u v → Q.Adj u v) :
    (M.edgeSet.ncard : Int) ≤ (Q.edgeSet.ncard : Int) := by
  have hle : M ≤ Q := SimpleGraph.le_iff_adj.mpr (by
    intro u v huv
    exact hMQ huv)
  have hcard : M.edgeSet.ncard ≤ Q.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono hle)
  exact_mod_cast hcard