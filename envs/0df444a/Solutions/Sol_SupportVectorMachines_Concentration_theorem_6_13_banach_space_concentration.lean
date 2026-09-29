-- Prove2me | solution 1 for SupportVectorMachines.Concentration.theorem_6_13_banach_space_concentration
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T06:43:15.310803+00:00
-- url     : https://prove2.me/submissions/2afab327-c709-4b87-8008-f409099014f3

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SVMdis

noncomputable def half : unitInterval := ⟨1/2, by norm_num, by norm_num⟩

lemma half_ne : half ≠ 0 := by
  intro h; have := congrArg Subtype.val h; norm_num [half] at this

lemma coe_half : ((half : unitInterval) : ℝ) = 1/2 := rfl

lemma w_eq (n : ℕ) : ((1 - (half:ℝ)) ^ n * (half:ℝ)) = (1/2:ℝ)^n * (1/2) := by
  rw [coe_half]; norm_num

lemma hgeo : HasSum (fun n : ℕ => (n:ℝ) * (1/2:ℝ)^n) 2 := by
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2:ℝ)) (by norm_num [abs_of_pos])
  have e : (1/2:ℝ) / (1 - 1/2)^2 = 2 := by norm_num
  rw [e] at h; exact h

lemma mean_eq : ∫ k, (k:ℝ) ∂(geometricMeasure half) = 1 := by
  rw [integral_geometricMeasure half_ne]
  simp only [w_eq, smul_eq_mul]
  have h2 := hgeo.mul_right (1/2)
  rw [show (2:ℝ) * (1/2) = 1 by norm_num] at h2
  have e : (fun n : ℕ => (1/2:ℝ)^n * (1/2) * (n:ℝ)) =
      (fun i : ℕ => (i:ℝ) * (1/2)^i * (1/2)) := by funext n; ring
  rw [e]; exact h2.tsum_eq

lemma not_summ : ¬ Summable (fun n : ℕ =>
    ((1/2:ℝ)^n * (1/2)) * (Real.exp (3 * (n:ℝ)) - 1 - 3 * (n:ℝ))) := by
  intro hs
  have hX : Summable (fun n : ℕ => ((1/2:ℝ)^n * (1/2)) * (1 + 3 * (n:ℝ))) := by
    have h1 := hgeo.summable
    have h0 : Summable (fun n : ℕ => (1/2:ℝ)^n) := summable_geometric_two
    exact ((h0.mul_right (1/2)).add (h1.mul_right (3/2))).congr fun n => by ring
  have hg := hs.add hX
  have ht := hg.tendsto_atTop_zero
  have hge : ∀ n : ℕ, (1/2:ℝ) ≤ ((1/2:ℝ)^n * (1/2)) * (Real.exp (3 * (n:ℝ)) - 1 - 3 * (n:ℝ))
      + ((1/2:ℝ)^n * (1/2)) * (1 + 3 * (n:ℝ)) := by
    intro n
    have e : ((1/2:ℝ)^n * (1/2)) * (Real.exp (3 * (n:ℝ)) - 1 - 3 * (n:ℝ))
        + ((1/2:ℝ)^n * (1/2)) * (1 + 3 * (n:ℝ)) = (1/2) * ((1/2)^n * Real.exp (3 * n)) := by ring
    rw [e]
    have : (1:ℝ) ≤ (1/2)^n * Real.exp (3 * n) := by
      rw [show Real.exp (3 * (n:ℝ)) = Real.exp 3 ^ n by rw [← Real.exp_nat_mul, mul_comm]]
      rw [← mul_pow]
      apply one_le_pow₀
      have : (4:ℝ) ≤ Real.exp 3 := by have := Real.add_one_le_exp 3; linarith
      linarith
    linarith
  have := ht.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 this
  linarith [hN N le_rfl, hge N]

lemma expint_zero : ∫ k, (Real.exp (3 * ‖(k:ℝ)‖) - 1 - 3 * ‖(k:ℝ)‖) ∂(geometricMeasure half) = 0 := by
  rw [integral_geometricMeasure half_ne]
  simp only [w_eq, smul_eq_mul, Real.norm_eq_abs, Nat.abs_cast]
  exact tsum_eq_zero_of_not_summable not_summ

theorem counter : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E]
    (n : ℕ)
    (ξ : Fin n → Ω → E) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hint : ∀ i, Integrable (ξ i) P) (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : 0 ≤ t),
    P.real {ω | ε * n ≤ ‖∑ i, ξ i ω‖} ≤
      Real.exp (-t * ε * n + t * (∫ ω, ‖∑ i, ξ i ω‖ ∂P) +
        ∑ i, ∫ ω, (Real.exp (t * ‖ξ i ω‖) - 1 - t * ‖ξ i ω‖) ∂P)) := by
  intro H
  have hint : Integrable (fun k : ℕ => (k:ℝ)) (geometricMeasure half) := by
    rw [integrable_geometricMeasure_iff half_ne]
    simp only [w_eq, Real.norm_eq_abs, Nat.abs_cast]
    exact (hgeo.summable.mul_right (1/2)).congr fun n => by ring
  have h := H (geometricMeasure half) (E := ℝ) 1 (fun _ k => (k:ℝ))
    (fun _ => measurable_of_countable _) iIndepFun.of_subsingleton (fun _ => hint)
    3 (by norm_num) 3 (by norm_num)
  simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, mul_one] at h
  have hm : ∫ ω, ‖(ω:ℝ)‖ ∂(geometricMeasure half) = 1 := by
    simp only [Real.norm_eq_abs, Nat.abs_cast]; exact mean_eq
  rw [hm, expint_zero] at h
  have hlow : (1/16:ℝ) ≤ (geometricMeasure half).real {ω : ℕ | (3:ℝ) ≤ ‖(ω:ℝ)‖} := by
    have hsub : ({3} : Set ℕ) ⊆ {ω : ℕ | (3:ℝ) ≤ ‖(ω:ℝ)‖} := by
      intro x hx; simp at hx; subst hx; norm_num
    have := measureReal_mono hsub (μ := geometricMeasure half)
    rw [geometricMeasure_real_singleton half_ne, w_eq] at this
    norm_num at this ⊢; linarith
  have hexp : Real.exp (-3 * 3 + 3 * 1 + 0) < 1/16 := by
    have : (-3 * 3 + 3 * 1 + 0 : ℝ) = -6 := by norm_num
    rw [this, Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 6) (by norm_num)]
    have h1 := Real.add_one_le_exp 1
    have : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have : (2:ℝ) ≤ Real.exp 1 := by linarith
    calc (1/16:ℝ)⁻¹ = 16 := by norm_num
      _ < 2 ^ 6 := by norm_num
      _ ≤ Real.exp 1 ^ 6 := by gcongr
  exact absurd h (not_le.mpr (lt_of_lt_of_le hexp hlow))

end SVMdis

/-- Counterexample: `Ω = ℕ` with the geometric distribution of parameter `1/2`, `E = ℝ`, `n = 1`,
`ξ₀(k) = k`, `ε = t = 3`. Then `E e^{3ξ₀} = ∞`, so the Bochner integral in the bound is `0`,
and the right-hand side is `exp(-9 + 3·Eξ₀) = exp(-6) < 1/16 = P(ξ₀ = 3) ≤ P(ξ₀ ≥ 3)`. -/
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E]
    (n : ℕ)
    (ξ : Fin n → Ω → E) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hint : ∀ i, Integrable (ξ i) P) (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : 0 ≤ t),
    P.real {ω | ε * n ≤ ‖∑ i, ξ i ω‖} ≤
      Real.exp (-t * ε * n + t * (∫ ω, ‖∑ i, ξ i ω‖ ∂P) +
        ∑ i, ∫ ω, (Real.exp (t * ‖ξ i ω‖) - 1 - t * ‖ξ i ω‖) ∂P)) :=
  SVMdis.counter
