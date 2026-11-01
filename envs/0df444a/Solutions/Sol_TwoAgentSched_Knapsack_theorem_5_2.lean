-- Prove2me | solution 1 for TwoAgentSched.Knapsack.theorem_5_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:16:50.320982+00:00
-- url     : https://prove2.me/submissions/ba5d463d-e952-4231-9bee-b86089152b28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TwoAgentSched_Knapsack_Problem51
import Definitions.Def_TwoAgentSched_Knapsack_Model
import Definitions.Def_TwoAgentSched_Knapsack_Construction
import Theorems.Thm_TwoAgentSched_Knapsack_knapsack_encoding_reduction
import Theorems.Thm_TwoAgentSched_Knapsack_theorem_5_2_equivalence

open TwoAgentSched.Knapsack CookPvsNP ProjSchedTW.Complexity

theorem solution : PolyReducible knapsackLang targetLang := by
  rcases knapsack_encoding_reduction with ⟨f, hf_poly, hf_iff⟩
  refine ⟨f, hf_poly, fun x => ?_⟩
  rw [← hf_iff x]
  constructor
  · rintro ⟨n, u, w, b, W, hyes, rfl⟩
    by_cases hpos : 0 < ∑ i, w i * u i
    · exact Or.inl ⟨n, u, w, b, W, hpos, (theorem_5_2_equivalence u w b W hpos).mp hyes, rfl⟩
    · exact Or.inr ⟨n, u, w, b, W, Nat.eq_zero_of_not_pos hpos, hyes, rfl⟩
  · rintro (⟨n, u, w, b, W, hpos, hrec, hx⟩ | ⟨n, u, w, b, W, _, hyes, hx⟩)
    · exact ⟨n, u, w, b, W, (theorem_5_2_equivalence u w b W hpos).mpr hrec, hx⟩
    · exact ⟨n, u, w, b, W, hyes, hx⟩
