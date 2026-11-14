-- Prove2me | solution 1 for StabilityDichotomies.Approximability.integrated_monotone_bernoulli_influences
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:10:24.091677+00:00
-- url     : https://prove2.me/submissions/052d1352-34f8-4b69-823b-d23dfc28200c

import Theorems.Thm_StabilityDichotomies_Approximability_finite_bernoulli_influence_derivative
import Theorems.Thm_StabilityDichotomies_Approximability_weighted_influence_integral_bound
import Theorems.Thm_StabilityDichotomies_Approximability_bernoulli_influence_nonnegative
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Approximability

private def weight {ι : Type} [Fintype ι] (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ j, if x j then p else 1-p
private def potential {ι : Type} [Fintype ι] (h : (ι → Bool) → ℝ) (p : ℝ) : ℝ :=
  ∑ x : ι → Bool, h x * weight p x
private def influence {ι : Type} [Fintype ι] (h : (ι → Bool) → ℝ) (p : ℝ) : ℝ :=
  ∑ i : ι, ∑ x : ι → Bool, weight p x *
    (h (Function.update x i true) - h (Function.update x i false))

private theorem weights_sum {ι : Type} [Fintype ι] (p : ℝ) :
    (∑ x : ι → Bool, weight p x) = 1 := by
  unfold weight
  have h := (Fintype.prod_sum (fun _ : ι => fun b : Bool => if b then p else 1-p)).symm
  simpa using h

private theorem weight_nonneg {ι : Type} [Fintype ι] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : ι → Bool) : 0 ≤ weight p x := by
  unfold weight
  apply Finset.prod_nonneg
  intro j hj
  split_ifs <;> linarith

private theorem potential_bounds {ι : Type} [Fintype ι] (h : (ι → Bool) → ℝ) (B p : ℝ)
    (hrange : ∀ x, 0 ≤ h x ∧ h x ≤ B) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ potential h p ∧ potential h p ≤ B := by
  constructor
  · apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (hrange x).1 (weight_nonneg p hp0 hp1 x)
  · calc
      _ ≤ ∑ x : ι → Bool, B * weight p x := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_right (hrange x).2 (weight_nonneg p hp0 hp1 x)
      _ = B := by rw [← Finset.mul_sum, weights_sum, mul_one]

theorem solution {ι : Type} [Fintype ι]
    (h : (ι → Bool) → ℝ) (B ε : ℝ) (hmono : Monotone h)
    (hrange : ∀ x, 0 ≤ h x ∧ h x ≤ B) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ p in (1-ε)..1, p * ∑ i : ι, ∑ x : ι → Bool,
      (∏ j : ι, if x j then p else 1-p) *
      (h (Function.update x i true) - h (Function.update x i false))) ≤ B := by
  have hc (x : ι → Bool) : Continuous (fun p => weight p x) := by
    unfold weight
    apply continuous_finsetProd
    intro j hj
    cases hx : x j <;> simp only [hx, Bool.false_eq_true, ↓reduceIte]
    · exact continuous_const.sub continuous_id
    · exact continuous_id
  have hd : Continuous (influence h) := by
    unfold influence
    fun_prop
  have hderiv (p : ℝ) : HasDerivAt (potential h) (influence h p) p := by
    change HasDerivAt (fun t => ∑ x : ι → Bool, h x * ∏ j, if x j then t else 1-t)
      (∑ i : ι, ∑ x : ι → Bool, (∏ j, if x j then p else 1-p) *
        (h (Function.update x i true) - h (Function.update x i false))) p
    exact finite_bernoulli_influence_derivative h p
  have hn (p : ℝ) (hp : p ∈ Set.Icc (1-ε) 1) : 0 ≤ influence h p := by
    apply bernoulli_influence_nonnegative h hmono p (by linarith [hp.1]) hp.2
  have hb : potential h 1 - potential h (1-ε) ≤ B := by
    have h1 := (potential_bounds h B 1 hrange (by norm_num) (by norm_num)).2
    have h0 := (potential_bounds h B (1-ε) hrange (by linarith) (by linarith)).1
    linarith
  have hh := weighted_influence_integral_bound ε B hε0 (potential h) (influence h)
    (by intro p hp; exact hderiv p) (hd.intervalIntegrable _ _) hn hb
  exact hh
