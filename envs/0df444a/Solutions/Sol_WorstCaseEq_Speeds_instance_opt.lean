-- Prove2me | solution 1 for WorstCaseEq.Speeds.instance_opt
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:29:50.195829+00:00
-- url     : https://prove2.me/submissions/e9ae54d9-5412-41f8-8a34-34c2fbf9b085

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

open WorstCaseEq.Speeds

theorem solution (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    opt (instWeights s₁ s₂) (speeds s₁ s₂) = 1 := by
  classical
  have hm (a : Fin 2 → Fin 2) :
      makespan (instWeights s₁ s₂) (speeds s₁ s₂) a =
        max (((if a 0 = 0 then s₂ else 0) + (if a 1 = 0 then s₁ else 0)) / s₁)
          (((if a 0 = 1 then s₂ else 0) + (if a 1 = 1 then s₁ else 0)) / s₂) := by
    simp [makespan, WorstCaseEq.Identical.load, instWeights, speeds,
      Fin.univ_succ, Finset.sup'_insert, Finset.sum_filter]
  have hl (a : Fin 2 → Fin 2) : 1 ≤ makespan (instWeights s₁ s₂) (speeds s₁ s₂) a := by
    rw [hm]
    generalize h0 : a 0 = i0
    generalize h1 : a 1 = i1
    fin_cases i0 <;> fin_cases i1 <;> simp [ne_of_gt h₁, ne_of_gt h₂]
    · left
      apply (le_div_iff₀ h₁).2
      linarith
    · by_cases h : s₁ ≤ s₂
      · left
        exact (le_div_iff₀ h₁).2 (by simpa using h)
      · right
        exact (le_div_iff₀ h₂).2 (by linarith)
    · right
      apply (le_div_iff₀ h₂).2
      linarith
  apply le_antisymm
  · have he : makespan (instWeights s₁ s₂) (speeds s₁ s₂) ![1, 0] = 1 := by
      rw [hm]; simp [ne_of_gt h₁, ne_of_gt h₂]
    unfold opt
    exact he ▸ Finset.inf'_le _ (Finset.mem_univ ![1, 0])
  · exact Finset.le_inf' _ _ (fun a _ => hl a)




#print axioms solution
