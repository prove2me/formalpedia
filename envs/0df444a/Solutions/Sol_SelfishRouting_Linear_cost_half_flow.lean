-- Prove2me | solution 1 for SelfishRouting.Linear.cost_half_flow
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:19:43.459542+00:00
-- url     : https://prove2.me/submissions/95a7f5ea-fbf4-49bd-b68d-e1545c015400

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

set_option autoImplicit false

open KellyStochasticNetworks SelfishRouting.Linear

lemma srl_linkFlow_half {J R : ℕ} (A : Fin J → Fin R → ℝ) (x : Fin R → ℝ) (j : Fin J) :
    linkFlow A (fun r => x r / 2) j = linkFlow A x j / 2 := by
  unfold linkFlow
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun r _ => by ring)

lemma srl_cost_eq {J R : ℕ} (A : Fin J → Fin R → ℝ) (ℓ : Fin J → ℝ → ℝ) (x : Fin R → ℝ) :
    SelfishRouting.Bicriteria.cost A ℓ x = ∑ j, ℓ j (linkFlow A x j) * linkFlow A x j := by
  unfold SelfishRouting.Bicriteria.cost SelfishRouting.Bicriteria.pathLatency linkFlow
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun r _ => by ring))

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (x : Fin R → ℝ) (hx : ∀ r, 0 ≤ x r) :
    SelfishRouting.Bicriteria.cost A (linLatency a b) x ≤ 4 * SelfishRouting.Bicriteria.cost A (linLatency a b) (fun r => x r / 2) := by
  rw [srl_cost_eq, srl_cost_eq, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hy : 0 ≤ linkFlow A x j := by
    unfold linkFlow
    refine Finset.sum_nonneg (fun r _ => ?_)
    rcases hA j r with h | h <;> rw [h] <;> simp [hx r]
  rw [srl_linkFlow_half]
  simp only [linLatency]
  have := mul_nonneg (hb j) hy
  have := mul_nonneg (ha j) (mul_nonneg hy hy)
  nlinarith
