-- Prove2me | solution 1 for RobustGeneralization.BernUpper.lemma24_inner_theta_lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:06:09.336756+00:00
-- url     : https://prove2.me/submissions/b8f9b9c9-47dd-4c58-9738-82ab59b6bd7e

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

lemma aux_l24_hoeff (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1/2) (l : ℝ) :
    (1/2 + τ) * Real.exp (-l) + (1/2 - τ) * Real.exp l ≤ Real.exp (l^2/2 - 2*τ*l) := by
  set p : unitInterval := ⟨1/2 + τ, by constructor <;> linarith⟩ with hp
  set μ : MeasureTheory.Measure Bool := ProbabilityTheory.bernoulliMeasure true false p with hμ
  set X : Bool → ℝ := fun b => if b then 1 else -1 with hXdef
  have hX : ∀ᵐ b ∂μ, X b ∈ Set.Icc (-1:ℝ) 1 := by
    refine Filter.Eventually.of_forall (fun b => ?_)
    cases b <;> simp [X]
  have hH := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := X)
    (Measurable.of_discrete.aemeasurable) hX
  have hint : ∀ f : Bool → ℝ, ∫ b, f b ∂μ = (1/2 + τ) * f true + (1/2 - τ) * f false := by
    intro f
    rw [hμ, ProbabilityTheory.integral_bernoulliMeasure]
    simp only [smul_eq_mul]
    show (1/2+τ) * f true + (1 - (1/2+τ)) * f false = _
    ring
  have hm := hH.mgf_le (-l)
  unfold ProbabilityTheory.mgf at hm
  rw [hint, hint] at hm
  simp only [X, if_true, Bool.false_eq_true, if_false] at hm
  norm_num at hm
  have e1 : Real.exp (-(l * (1 - (1 / 2 + τ + (τ - 1 / 2))))) = Real.exp (-l) * Real.exp (2*τ*l) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(l * (-1 - (1 / 2 + τ + (τ - 1 / 2))))) = Real.exp l * Real.exp (2*τ*l) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2] at hm
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)]
  linarith

noncomputable def aux_l24_M (τ l : ℝ) : ℝ := (1/2 + τ) * Real.exp (-l) + (1/2 - τ) * Real.exp l

lemma aux_l24_inner {d : ℕ} (θ : Fin d → Bool) (p : (Fin d → Bool) × Bool) :
    inner ℝ (zvec p) (pm θ) = ∑ i, lab (decide (p.1 i = (p.2 == θ i))) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases p with ⟨s, y⟩
  simp only [zvec, pm, PiLp.smul_apply, smul_eq_mul]
  have h : ∀ a b c : Bool, inner ℝ (lab c * lab a) (lab b) = lab (decide (a = (c == b))) := by
    intro a b c; cases a <;> cases b <;> cases c <;> simp [lab]
  exact h _ _ _

lemma aux_l24_G {d : ℕ} (θ : Fin d → Bool) (τ l : ℝ) (y : Bool) (i : Fin d) :
    ∑ b : Bool, ((if b = (y == θ i) then 1/2 + τ else 1/2 - τ) *
      Real.exp (-(l * lab (decide (b = (y == θ i)))))) = aux_l24_M τ l := by
  rw [Fintype.sum_bool, aux_l24_M]
  cases y <;> cases θ i <;> simp [lab] <;> ring

lemma aux_l24_sum {d : ℕ} (θ : Fin d → Bool) (τ l : ℝ) :
    ∑ p : (Fin d → Bool) × Bool, bernW θ τ p *
      Real.exp (-(l * ∑ i, lab (decide (p.1 i = (p.2 == θ i))))) = aux_l24_M τ l ^ d := by
  have key : ∀ p : (Fin d → Bool) × Bool, bernW θ τ p *
      Real.exp (-(l * ∑ i, lab (decide (p.1 i = (p.2 == θ i))))) =
      (1/2) * ∏ i, ((if p.1 i = (p.2 == θ i) then 1/2 + τ else 1/2 - τ) *
        Real.exp (-(l * lab (decide (p.1 i = (p.2 == θ i)))))) := by
    intro p
    rw [bernW, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    ring
  simp_rw [key]
  rw [Fintype.sum_prod_type_right]
  have hy : ∀ y : Bool, ∑ s : Fin d → Bool, (1/2 : ℝ) * ∏ i, ((if s i = (y == θ i) then 1/2 + τ else 1/2 - τ) *
        Real.exp (-(l * lab (decide (s i = (y == θ i)))))) = (1/2) * aux_l24_M τ l ^ d := by
    intro y
    rw [← Finset.mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun i (b : Bool) => ((if b = (y == θ i) then 1/2 + τ else 1/2 - τ) *
        Real.exp (-(l * lab (decide (b = (y == θ i)))))))]
    simp_rw [aux_l24_G]
    simp
  simp only at hy ⊢
  simp_rw [hy]
  rw [Fintype.sum_bool]
  ring


lemma aux_l24_bW_nonneg {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/2)
    (p : (Fin d → Bool) × Bool) : 0 ≤ bernW θ τ p := by
  unfold bernW
  apply mul_nonneg (by norm_num)
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

lemma aux_l24_chernoff {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/2)
    (l c : ℝ) (hl : 0 ≤ l) :
    bprob θ τ (fun p => inner ℝ (zvec p) (pm θ) ≤ c) ≤ Real.exp (l * c) * aux_l24_M τ l ^ d := by
  rw [← aux_l24_sum θ τ l, Finset.mul_sum]
  unfold bprob
  apply Finset.sum_le_sum
  intro p _
  have hw := aux_l24_bW_nonneg θ τ hτ hτ' p
  rw [mul_left_comm, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hw
  split_ifs with h
  · apply Real.one_le_exp
    simp only at h
    rw [aux_l24_inner] at h
    nlinarith
  · exact (Real.exp_pos _).le

end RobustGeneralization.BernUpper

open RobustGeneralization.BernUpper

theorem solution {d : ℕ} (hd : 1 ≤ d) (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) (δ : ℝ) (hδ : 0 < δ) :
    bprob θ τ (fun p => inner ℝ (zvec p) (pm θ)
        ≤ 2 * τ * d - Real.sqrt (2 * d * Real.log (1 / δ))) ≤ δ := by
  rcases le_or_gt 1 δ with h1 | h1
  · have := aux_l24_chernoff θ τ hτ.le hτ' 0
      (2 * τ * d - Real.sqrt (2 * d * Real.log (1 / δ))) le_rfl
    have hM : aux_l24_M τ 0 = 1 := by simp [aux_l24_M]; ring
    rw [hM, zero_mul, Real.exp_zero, one_pow, mul_one] at this
    linarith
  · set L := Real.log (1/δ) with hL
    have hLpos : 0 < L := Real.log_pos (one_lt_one_div hδ h1)
    have hdpos : (0:ℝ) < d := by exact_mod_cast hd
    set t := Real.sqrt (2 * d * L) with ht
    have ht2 : t^2 = 2 * d * L := Real.sq_sqrt (by positivity)
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    set l := t / d with hl
    have hl0 : 0 ≤ l := div_nonneg ht0 hdpos.le
    have hC := aux_l24_chernoff θ τ hτ.le hτ' l (2 * τ * d - t) hl0
    have hMle : aux_l24_M τ l ^ d ≤ Real.exp (l^2/2 - 2*τ*l) ^ d := by
      apply pow_le_pow_left₀ _ (aux_l24_hoeff τ hτ.le hτ' l)
      have := Real.exp_pos l
      have := Real.exp_pos (-l)
      have h3 : 0 ≤ 1/2 - τ := by linarith
      positivity
    calc _ ≤ Real.exp (l * (2 * τ * d - t)) * aux_l24_M τ l ^ d := hC
      _ ≤ Real.exp (l * (2 * τ * d - t)) * Real.exp (l^2/2 - 2*τ*l) ^ d :=
          mul_le_mul_of_nonneg_left hMle (Real.exp_pos _).le
      _ = Real.exp (l * (2 * τ * d - t) + d * (l^2/2 - 2*τ*l)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ = Real.exp (-L) := by
          congr 1
          rw [hl]
          field_simp
          linear_combination (-1) * ht2
      _ = δ := by
          rw [hL, Real.exp_neg, Real.exp_log (by positivity)]
          simp
