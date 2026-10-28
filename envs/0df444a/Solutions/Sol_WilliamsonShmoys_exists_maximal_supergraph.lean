-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:38:09.427059+00:00
-- url     : https://prove2.me/submissions/e4b9b781-988e-418e-86b4-48c1b0587bb8

import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Fintype.Sigma
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hL : P L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ P M ∧
      ∀ N : SimpleGraph V, M ≤ N → P N → N = M := by
  classical
  have hfin : ({J : SimpleGraph V | L ≤ J ∧ P J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨L, le_rfl, hL⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩
