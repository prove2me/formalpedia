-- Prove2me | solution 1 for StrongWeakEq.TwoState.display_4_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:40:43.96125+00:00
-- url     : https://prove2.me/submissions/d615293e-ff2e-4307-b924-9b86b6610bcb

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder
import Definitions.Def_StrongWeakEq_TwoState_TwoStateModel

open StrongWeakEq.TwoState in
theorem solution (lam ρ ρ' : ℝ) (hlam : 0 < lam ∧ lam < 1) (hρ : 0 ≤ ρ) (hρ' : 0 ≤ ρ')
    (g₁ g₂ : ℝ → ℝ) (a b as bs : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (has : 0 ≤ as) (hbs : 0 ≤ bs) :
    StrongWeakEq.Existence.Gamma (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 0 (gen a b 0)
      = g₁ a - a * (StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 0
                      - StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 1) ∧
    StrongWeakEq.Existence.Gamma (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 1 (gen a b 1)
      = g₂ b + b * (StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 0
                      - StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 1) ∧
    StrongWeakEq.Existence.Lambda (twoStatePayoff lam ρ ρ' g₁ g₂) (twoStatePayoffDeriv lam ρ ρ' g₁ g₂) (gen as bs) 1
        (gen a b)
      = 2 * b * (StrongWeakEq.Existence.payoffDeriv (twoStatePayoffDeriv lam ρ ρ' g₁ g₂) (gen as bs) 0
                  - StrongWeakEq.Existence.payoffDeriv (twoStatePayoffDeriv lam ρ ρ' g₁ g₂) (gen as bs) 1)
        + b * (g₁ a - g₂ b) - (ρ * lam + ρ' * (1 - lam)) * g₂ b
        - (b ^ 2 + a * b) * (StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 0
                              - StrongWeakEq.Existence.payoff (twoStatePayoff lam ρ ρ' g₁ g₂) (gen as bs) 1) := by
  have hf0 : ∀ t q, twoStatePayoff lam ρ ρ' g₁ g₂ t 0 q = discount lam ρ ρ' t * g₁ (q 1) := by
    intro t q; simp [twoStatePayoff]
  have hf1 : ∀ t q, twoStatePayoff lam ρ ρ' g₁ g₂ t 1 q = discount lam ρ ρ' t * g₂ (q 0) := by
    intro t q; simp [twoStatePayoff]
  have hfd1 : ∀ t q, twoStatePayoffDeriv lam ρ ρ' g₁ g₂ t 1 q
      = discountDeriv lam ρ ρ' t * g₂ (q 0) := by
    intro t q; simp [twoStatePayoffDeriv]
  have hd0 : discount lam ρ ρ' 0 = 1 := by
    simp only [discount, mul_zero, Real.exp_zero]; ring
  have hdd0 : discountDeriv lam ρ ρ' 0 = -(ρ * lam + ρ' * (1 - lam)) := by
    simp only [discountDeriv, mul_zero, Real.exp_zero]; ring
  have e00 : gen a b 0 0 = -a := by simp [gen]
  have e01 : gen a b 0 1 = a := by simp [gen]
  have e10 : gen a b 1 0 = b := by simp [gen]
  have e11 : gen a b 1 1 = -b := by simp [gen]
  simp only [StrongWeakEq.Existence.Gamma, StrongWeakEq.Existence.Lambda, dotProduct,
    Fin.sum_univ_two, hf0, hf1, hfd1, hd0, hdd0, e00, e01, e10, e11]
  refine ⟨by ring, by ring, by ring⟩
