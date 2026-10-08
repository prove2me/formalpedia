-- Prove2me | solution 1 for PoAIndep.Topology.cost_eq_sum_edges
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:07:35.801525+00:00
-- url     : https://prove2.me/submissions/32d6b39e-4960-4bf6-9ba0-6cb80ba7f210

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

open PoAIndep.Topology

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f : Flow I) (hf : IsFlow I f) :
    cost I f = ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I f e := by
  classical
  have hp (i : Fin I.k) (P : List E) (hP : P ∈ (f i).support) :
      pathLatency I f P = ∑ e, if e ∈ P then I.ℓ e (edgeFlow I f e) else 0 := by
    have hn : P.Nodup := ((hf i).2 P hP).2.2.2.2.tail.of_map
    unfold pathLatency
    rw [← List.sum_toFinset _ hn]
    rw [← Finset.sum_filter]
    congr 1
    ext e
    simp
  unfold cost Finsupp.sum
  calc
    _ = ∑ i, ∑ P ∈ (f i).support, ∑ e,
        I.ℓ e (edgeFlow I f e) * (if e ∈ P then f i P else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro P hP
      dsimp only
      rw [hp i P hP, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp
    _ = ∑ i, ∑ e, ∑ P ∈ (f i).support,
        I.ℓ e (edgeFlow I f e) * (if e ∈ P then f i P else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I f e := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      unfold edgeFlow Finsupp.sum
      simp_rw [Finset.mul_sum]



#print axioms solution
