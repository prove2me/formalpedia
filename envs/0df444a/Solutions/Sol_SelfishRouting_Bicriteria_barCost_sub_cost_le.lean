-- Prove2me | solution 1 for SelfishRouting.Bicriteria.barCost_sub_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:25:51.004989+00:00
-- url     : https://prove2.me/submissions/157d7dc4-a92a-461d-a037-01f149d47827

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model
import Definitions.Def_SelfishRouting_Bicriteria_BarLatency

set_option autoImplicit false
open KellyStochasticNetworks SelfishRouting.Bicriteria

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (x y : Fin R → ℝ) (hx : ∀ r, 0 ≤ x r) (hy : ∀ r, 0 ≤ y r) :
    (∑ j, barLatency ℓ (linkFlow A x) j (linkFlow A y j) * linkFlow A y j) - cost A ℓ y
      ≤ cost A ℓ x := by
  have hcost : ∀ z : Fin R → ℝ, cost A ℓ z = ∑ j, ℓ j (linkFlow A z j) * linkFlow A z j := by
    intro z
    unfold cost pathLatency linkFlow
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hnn : ∀ z : Fin R → ℝ, (∀ r, 0 ≤ z r) → ∀ j, 0 ≤ linkFlow A z j := by
    intro z hz j
    unfold linkFlow
    refine Finset.sum_nonneg fun r _ => ?_
    rcases hA j r with h | h <;> rw [h] <;> simp [hz r]
  rw [hcost x, hcost y, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := hnn x hx j
  have h2 := hnn y hy j
  have h3 := hℓnn j _ h1
  have h4 := hℓnn j _ h2
  unfold barLatency
  split_ifs with h
  · nlinarith [mul_nonneg h4 h2, mul_le_mul_of_nonneg_left h h3]
  · push_neg at h
    nlinarith [mul_nonneg h3 h1, mul_nonneg h4 h2]
