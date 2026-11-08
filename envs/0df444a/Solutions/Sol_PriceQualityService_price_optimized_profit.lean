-- Prove2me | solution 1 for PriceQualityService.price_optimized_profit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:15:42.710976+00:00
-- url     : https://prove2.me/submissions/d34ab311-663f-4352-8b13-50119f35fa67

import Mathlib
import Definitions.Def_PriceQualityService_profit
import Definitions.Def_PriceQualityService_netValue
import Definitions.Def_PriceQualityService_optPrice

open PriceQualityService in
theorem solution {N : ℕ} (α s a b c q t : Fin N → ℝ) (r : ℝ)
    (hr : r = ∑ i, Real.exp (netValue α s a b c q t i - r - 1)) :
    (∀ p : Fin N → ℝ, profit α s a b c p q t ≤ r) ∧
      profit α s a b c (optPrice a b c q t r) q t = r := by
  have hu : ∀ p i, utility α s p q t i =
      netValue α s a b c q t i - margin a b c p q t i := by
    intro p i
    unfold utility netValue margin
    ring
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  have key : ∀ y v : ℝ, (y - r) * Real.exp (v - y) ≤ Real.exp (v - r - 1) := by
    intro y v
    have h1 := Real.add_one_le_exp (y - r - 1)
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (v - y)).le
    rw [← Real.exp_add] at h2
    have e : y - r - 1 + (v - y) = v - r - 1 := by ring
    rw [e] at h2
    have e2 : (y - r - 1 + 1) * Real.exp (v - y) = (y - r) * Real.exp (v - y) := by ring
    linarith
  constructor
  · intro p
    unfold profit choiceProb
    have hD : 0 < 1 + ∑ j, Real.exp (utility α s p q t j) :=
      add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le))
    have hsum : ∑ i, margin a b c p q t i *
        (Real.exp (utility α s p q t i) / (1 + ∑ j, Real.exp (utility α s p q t j))) =
        (∑ i, margin a b c p q t i * Real.exp (utility α s p q t i)) /
          (1 + ∑ j, Real.exp (utility α s p q t j)) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hsum, div_le_iff₀ hD]
    have hterm : ∀ i, (margin a b c p q t i - r) * Real.exp (utility α s p q t i) ≤
        Real.exp (netValue α s a b c q t i - r - 1) := by
      intro i
      rw [hu]
      exact key _ _
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    rw [← hr] at hs
    have hsplit : ∑ i, (margin a b c p q t i - r) * Real.exp (utility α s p q t i) =
        ∑ i, margin a b c p q t i * Real.exp (utility α s p q t i) -
          r * ∑ i, Real.exp (utility α s p q t i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hsplit] at hs
    nlinarith
  · unfold profit choiceProb
    have hm : ∀ i, margin a b c (optPrice a b c q t r) q t i = 1 + r := by
      intro i
      unfold margin optPrice
      ring
    have hu' : ∀ i, utility α s (optPrice a b c q t r) q t i =
        netValue α s a b c q t i - r - 1 := by
      intro i
      rw [hu, hm]
      ring
    simp only [hm, hu']
    rw [← hr]
    have h1r : (1 + r) ≠ 0 := by linarith
    have hsimp : ∑ i, (1 + r) * (Real.exp (netValue α s a b c q t i - r - 1) / (1 + r)) =
        ∑ i, Real.exp (netValue α s a b c q t i - r - 1) :=
      Finset.sum_congr rfl (fun i _ => mul_div_cancel₀ _ h1r)
    rw [hsimp]
    exact hr.symm
