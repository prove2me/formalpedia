-- Prove2me | solution 1 for WorstCaseEq.Speeds.instance_socialCost
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:30:06.445845+00:00
-- url     : https://prove2.me/submissions/1b9131eb-24df-43a6-9a04-dd706bc9d31c

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model
open WorstCaseEq.Speeds

theorem solution (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂) :
    socialCost (instWeights s₁ s₂) (speeds s₁ s₂) (instProfile s₁ s₂)
      = (s₁ + 2 * s₂) / (s₁ + s₂) := by
  classical
  have h₂ : 0 < s₂ := lt_of_lt_of_le h₁ h₁₂
  have hs : s₁ + s₂ ≠ 0 := by positivity
  have hu : (Finset.univ : Finset (Fin 2 → Fin 2)) =
      {![0,0], ![0,1], ![1,0], ![1,1]} := by decide
  have hj : (Finset.univ : Finset (Fin 2)) = {0,1} := by decide
  have hmax1 : max ((s₁+s₂)/s₁) 0 = (s₁+s₂)/s₁ := max_eq_left (by positivity)
  have hmax2 : max 0 ((s₁+s₂)/s₂) = (s₁+s₂)/s₂ := max_eq_right (by positivity)
  have hcross : s₁/s₂ ≤ s₂/s₁ := by
    apply (div_le_div_iff₀ h₂ h₁).mpr
    nlinarith
  have hn : max (s₂/s₁) (s₁/s₂) = s₂/s₁ := max_eq_left hcross
  unfold socialCost
  rw [hu]
  simp [AGT.profileProb, makespan, WorstCaseEq.Identical.load, instWeights,
    speeds, instProfile, hj, Fin.prod_univ_two, Fin.sum_univ_two,
    Finset.sum_filter, Finset.sup'_insert, Finset.sup'_singleton, add_comm s₂ s₁,
    hmax1, hmax2, hn, max_self]
  field_simp [h₁.ne', h₂.ne', hs]
  simp only [max_self]
  ring


#print axioms solution
