-- Prove2me | solution 1 for WilliamsonShmoys.bridge_strictly_enlarges_graph__p2m_a49e8573_7163_46f3_bc6a_b6dc614057e1_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:39:14.142779+00:00
-- url     : https://prove2.me/submissions/ea7b0940-c300-4fad-b504-9d072fcadb6e

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (u v : V)
    (huv : u ≠ v)
    (hnotadj : ¬ G.Adj u v) :
    G < G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v) := by
  classical
  let K : SimpleGraph V := SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)
  have hKuv : K.Adj u v := by
    simp [K, SimpleGraph.fromRel_adj, huv]
  have hsupuv : (G ⊔ K).Adj u v :=
    (SimpleGraph.sup_adj G K u v).2 (Or.inr hKuv)
  refine lt_of_le_of_ne le_sup_left ?_
  intro hEq
  have hback : (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)) ≤ G := by
    rw [← hEq]
  exact hnotadj (by simpa [K] using hback hsupuv)
