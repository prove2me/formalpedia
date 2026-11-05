-- Prove2me | solution 1 for TenChallenges.challenge_05_r2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:20.702132+00:00
-- url     : https://prove2.me/submissions/4f5abe6b-83c9-4791-bef4-63d993510c61

import Definitions.Def_TenChallenges_Challenge_05
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open SimpleGraph

/-- The path on two vertices has Erdős–Hajnal exponent one. -/
theorem solution : TenChallenges.statement_05 2 := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro V _ G hfree
  have hno : ∀ u v : V, ¬ G.Adj u v := by
    intro u v huv
    apply hfree
    rw [pathGraph_two_eq_top]
    refine ⟨{ toFun := ![u, v], inj' := ?_, map_rel_iff' := ?_ }⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [huv.ne, huv.ne.symm]
    · intro i j
      change G.Adj (![u, v] i) (![u, v] j) ↔ i ≠ j
      fin_cases i <;> fin_cases j <;> simp [huv, huv.symm]
  refine ⟨Finset.univ, Or.inr ?_, ?_⟩
  · intro u _ v _ huv
    exact ⟨huv, hno u v⟩
  · simp
