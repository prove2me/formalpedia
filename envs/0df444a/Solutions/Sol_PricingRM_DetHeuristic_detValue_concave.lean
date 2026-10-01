-- Prove2me | solution 1 for PricingRM.DetHeuristic.detValue_concave
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:40:23.578511+00:00
-- url     : https://prove2.me/submissions/618c0d71-3386-4889-af3d-76cda8627823

import Definitions.Def_PricingRM_DetHeuristic_PricingModel
import Mathlib.Analysis.Convex.Function

open PricingRM.DetHeuristic

theorem solution {N : ℕ} (M : PricingModel N)
    (hconc : ∀ n, ConcaveOn ℝ (Set.Ici 0) (fun p => p * meanDemand M n p))
    (hconv : ∀ n, ConvexOn ℝ (Set.Ici 0) (meanDemand M n))
    (C₁ C₂ : ℝ) (p₁ p₂ : Fin N → ℝ) (h₁ : IsDetOptimal M C₁ p₁) (h₂ : IsDetOptimal M C₂ p₂)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    ((θ * detObjective M p₁ + (1 - θ) * detObjective M p₂ : ℝ) : EReal) ≤
      detValue M (θ * C₁ + (1 - θ) * C₂) := by
  classical
  let p:Fin N→ℝ:=fun n=>θ*p₁ n+(1-θ)*p₂ n
  have hθ:0≤1-θ:=by linarith
  have hsum:θ+(1-θ)=1:=by ring
  have hp:DetFeasible M (θ*C₁+(1-θ)*C₂) p:=by
    constructor
    · intro n
      exact add_nonneg (mul_nonneg hθ₀ (h₁.1.1 n)) (mul_nonneg hθ (h₂.1.1 n))
    · calc
        _ ≤ ∑n,(θ*meanDemand M n (p₁ n)+(1-θ)*meanDemand M n (p₂ n)):=by
          apply Finset.sum_le_sum
          intro n hn
          exact (hconv n).2 (h₁.1.1 n) (h₂.1.1 n) hθ₀ hθ hsum
        _ = θ*(∑n,meanDemand M n (p₁ n))+(1-θ)*(∑n,meanDemand M n (p₂ n)):=by
          rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
        _ ≤ θ*C₁+(1-θ)*C₂:=add_le_add (mul_le_mul_of_nonneg_left h₁.1.2 hθ₀) (mul_le_mul_of_nonneg_left h₂.1.2 hθ)
  have hobj:θ*detObjective M p₁+(1-θ)*detObjective M p₂≤detObjective M p:=by
    unfold detObjective
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    exact (hconc n).2 (h₁.1.1 n) (h₂.1.1 n) hθ₀ hθ hsum
  exact (EReal.coe_le_coe_iff.mpr hobj).trans (le_iSup_of_le ⟨p,hp⟩ le_rfl)

