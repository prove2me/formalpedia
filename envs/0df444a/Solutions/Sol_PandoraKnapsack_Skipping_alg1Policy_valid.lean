-- Prove2me | solution 1 for PandoraKnapsack.Skipping.alg1Policy_valid
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:24:51.790825+00:00
-- url     : https://prove2.me/submissions/b7d06484-67af-4885-b344-0f0f8d365dee

import Definitions.Def_PandoraKnapsack_Skipping_RoundingPayoff

open PandoraKnapsack.Skipping
variable {n m T : ℕ}
private lemma order_distinct (a : Assignment n m T) :
    ((scanOrder a).map Prod.fst).Nodup := by
  apply ((List.mergeSort_perm (retained a) _).map Prod.fst).nodup_iff.mpr
  rw [List.Nodup, List.pairwise_map, retained, List.pairwise_filterMap]
  apply (List.nodup_finRange n).imp
  intro i k hik u hu v hv
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hu
  obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hv
  exact hik


theorem solution {n m T : ℕ} (a : Assignment n m T) : IsSkippingPolicy T (alg1Policy a) := by
  refine ⟨?_, ?_⟩
  · simpa [alg1Policy,List.map_map,Function.comp_def] using order_distinct a
  · intro e he
    obtain ⟨f,_,rfl⟩ := List.mem_map.mp he
    exact Nat.sub_le ..
