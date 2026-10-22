-- Prove2me | solution 1 for SelfishRouting.Linear.figure_3_pigou
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:19:44.639896+00:00
-- url     : https://prove2.me/submissions/f14575c7-33a1-4cf9-95d1-48f90d803d8b

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

set_option autoImplicit false

open KellyStochasticNetworks SelfishRouting.Linear SelfishRouting.Bicriteria

lemma srl_pig_link (y : Fin 2 → ℝ) (j : Fin 2) :
    linkFlow (fun j r : Fin 2 => if j = r then (1 : ℝ) else 0) y j = y j := by
  unfold linkFlow
  simp

lemma srl_pig_path (y : Fin 2 → ℝ) (r : Fin 2) :
    pathLatency (fun j r : Fin 2 => if j = r then (1 : ℝ) else 0) (linLatency ![0, 1] ![1, 0]) y r
      = linLatency ![0, 1] ![1, 0] r (y r) := by
  unfold pathLatency
  simp [srl_pig_link]

lemma srl_pig_cost (y : Fin 2 → ℝ) :
    cost (fun j r : Fin 2 => if j = r then (1 : ℝ) else 0) (linLatency ![0, 1] ![1, 0]) y
      = y 0 + y 1 * y 1 := by
  unfold cost
  simp [srl_pig_path, Fin.sum_univ_two, linLatency]

lemma srl_pig_feas (y : Fin 2 → ℝ) :
    y ∈ wardropFeasible (fun _ : Fin 2 => (0 : Fin 1)) (fun _ : Fin 1 => (1 : ℝ)) ↔
      0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 = 1 := by
  unfold wardropFeasible
  simp only [Set.mem_setOf_eq, Fin.forall_fin_two, Fin.forall_fin_one]
  simp [Fin.sum_univ_two]
  tauto

theorem solution :
    SelfishRouting.Bicriteria.IsNashFlow (fun j r : Fin 2 => if j = r then (1 : ℝ) else 0) (fun _ : Fin 2 => (0 : Fin 1))
        (linLatency ![0, 1] ![1, 0]) (fun _ => 1) ![0, 1] ∧
      SelfishRouting.Bicriteria.cost (fun j r : Fin 2 => if j = r then (1 : ℝ) else 0) (linLatency ![0, 1] ![1, 0])
        ![0, 1] = 1 ∧
      IsOptimalFlow (fun j r : Fin 2 => if j = r then (1 : ℝ) else 0)
        (fun _ : Fin 2 => (0 : Fin 1)) (linLatency ![0, 1] ![1, 0]) (fun _ => 1) ![1 / 2, 1 / 2] ∧
      SelfishRouting.Bicriteria.cost (fun j r : Fin 2 => if j = r then (1 : ℝ) else 0) (linLatency ![0, 1] ![1, 0])
        ![1 / 2, 1 / 2] = 3 / 4 := by
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [srl_pig_feas]; norm_num
  · intro r₁ r₂ _ hne δ hδ hδx
    rw [srl_pig_path, srl_pig_path]
    fin_cases r₁ <;> fin_cases r₂
    · exact absurd rfl hne
    · -- r₁ = 0: x 0 = 0 so δ ≤ 0 contradiction
      simp at hδx; linarith
    · simp [shiftFlow, linLatency]
    · exact absurd rfl hne
  · rw [srl_pig_cost]; norm_num
  · rw [srl_pig_feas]; norm_num
  · intro y hy
    rw [srl_pig_feas] at hy
    rw [srl_pig_cost, srl_pig_cost]
    obtain ⟨h0, h1, h2⟩ := hy
    have : y 0 = 1 - y 1 := by linarith
    simp
    rw [this]
    nlinarith [sq_nonneg (y 1 - 1/2)]
  · rw [srl_pig_cost]; norm_num
