-- Prove2me | solution 1 for RobustPower.Hypercube.theorem_5_4_robust_eq_adapt
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:56:57.340864+00:00
-- url     : https://prove2.me/submissions/1a3d9c4e-1e19-4d52-8486-2a5d0b8eec00

import Theorems.Thm_RobustPower_Hypercube_p31_adapt_le_rob
import Theorems.Thm_RobustPower_Hypercube_eq_5_8_5_10_worst_scenario
import Theorems.Thm_RobustPower_Hypercube_eq_5_11_5_13_corner_rob_feasible
import Theorems.Thm_RobustPower_Hypercube_eq_5_14_corner_cost_le_adapt_cost

open RobustPower.Hypercube

theorem solution
    {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ)
    (I₁ : Set (Fin n₁)) (I₂ : Set (Fin n₂))
    (c : Fin n₁ → ℝ) (d : Ω → Fin n₂ → ℝ)
    (hc : 0 ≤ c) (hd : ∀ ω, 0 ≤ d ω)
    (hU : IsHypercube (uncertaintySet A B b d)) :
    zRob A B b I₁ I₂ c d = zAdapt A B b I₁ I₂ c d := by
  apply le_antisymm
  · obtain ⟨ωbar, hA, hB, hb, hdbar⟩ := eq_5_8_5_10_worst_scenario A B b d hU
    unfold zAdapt
    refine le_iInf fun x => le_iInf fun y => le_iInf fun hxy => ?_
    have hrob := eq_5_11_5_13_corner_rob_feasible A B b I₁ I₂ ωbar hA hB hb x y hxy
    have hcost := eq_5_14_corner_cost_le_adapt_cost A B b I₁ I₂ c d hd ωbar hdbar x y hxy
    have hvalue : zRob A B b I₁ I₂ c d ≤ RobustPower.AdaptGap.robCost c d x (y ωbar) := by
      unfold zRob
      exact iInf_le_of_le x (iInf_le_of_le (y ωbar) (iInf_le_of_le hrob le_rfl))
    exact hvalue.trans hcost
  · exact p31_adapt_le_rob A B b I₁ I₂ c d hc hd
