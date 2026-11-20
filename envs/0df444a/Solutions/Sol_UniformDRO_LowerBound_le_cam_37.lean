-- Prove2me | solution 1 for UniformDRO.LowerBound.le_cam_37
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T16:01:48.550337+00:00
-- url     : https://prove2.me/submissions/01076814-cc9f-47e2-b12a-280b487ebede

import Mathlib
import Definitions.Def_UniformDRO_LowerBound_Setting

open MeasureTheory UniformDRO.LowerBound

lemma sampleProb_nonneg {n : ℕ} (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (b : Fin n → Bool) :
    0 ≤ sampleProb p b := by
  unfold sampleProb
  exact Finset.prod_nonneg (fun i _ => by split_ifs <;> linarith [hp.1, hp.2])

lemma sampleProb_sum {n : ℕ} (p : ℝ) : ∑ b : Fin n → Bool, sampleProb p b = 1 := by
  unfold sampleProb
  rw [← Fintype.prod_sum (fun (_ : Fin n) (x : Bool) => if x then p else 1 - p)]
  simp

theorem solution (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (M : ℝ) (hM : 0 < M) (n : ℕ)
    (p₀ p₁ δ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) (hp₁ : p₁ ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 < δ)
    (hsep : 2 * δ ≤ |UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₀) id -
      UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₁) id|) :
    ENNReal.ofReal (δ / 2 * (1 - tvDist n p₀ p₁)) ≤ minimaxRisk k ρ M n := by
  classical
  set r₀ := UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₀) id with hr₀
  set r₁ := UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p₁) id with hr₁
  unfold minimaxRisk
  refine le_iInf (fun R => ?_)
  set x₀ : (Fin n → Bool) → ℝ := fun b => |R (sampleVec M b) - r₀| with hx₀
  set x₁ : (Fin n → Bool) → ℝ := fun b => |R (sampleVec M b) - r₁| with hx₁
  set P₀ : (Fin n → Bool) → ℝ := fun b => sampleProb p₀ b with hP₀
  set P₁ : (Fin n → Bool) → ℝ := fun b => sampleProb p₁ b with hP₁
  have hE : ∀ (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (r : ℝ),
      r = UniformDRO.Concentration.robustRisk k ρ (twoPointLaw 0 M p) id →
      estRisk k ρ M n R p = ENNReal.ofReal (∑ b, sampleProb p b * |R (sampleVec M b) - r|) := by
    intro p hp r hr
    unfold estRisk
    rw [← hr, ENNReal.ofReal_sum_of_nonneg (fun b _ => mul_nonneg (sampleProb_nonneg p hp b) (abs_nonneg _))]
  have hE0 := hE p₀ hp₀ r₀ hr₀
  have hE1 := hE p₁ hp₁ r₁ hr₁
  have hsup0 : estRisk k ρ M n R p₀ ≤ ⨆ p ∈ Set.Icc (0 : ℝ) 1, estRisk k ρ M n R p :=
    le_iSup₂ (f := fun p (_ : p ∈ Set.Icc (0 : ℝ) 1) => estRisk k ρ M n R p) p₀ hp₀
  have hsup1 : estRisk k ρ M n R p₁ ≤ ⨆ p ∈ Set.Icc (0 : ℝ) 1, estRisk k ρ M n R p :=
    le_iSup₂ (f := fun p (_ : p ∈ Set.Icc (0 : ℝ) 1) => estRisk k ρ M n R p) p₁ hp₁
  -- real lower bound for the average risk
  have hmin : ∀ b, min (P₀ b) (P₁ b) * (2 * δ) ≤ P₀ b * x₀ b + P₁ b * x₁ b := by
    intro b
    have htri : 2 * δ ≤ x₀ b + x₁ b := by
      refine hsep.trans ?_
      have := abs_sub_le r₀ (R (sampleVec M b)) r₁
      simp only [hx₀, hx₁]; rw [abs_sub_comm (R (sampleVec M b)) r₀]; linarith
    have h0 := sampleProb_nonneg p₀ hp₀ b
    have h1 := sampleProb_nonneg p₁ hp₁ b
    have hx0 : 0 ≤ x₀ b := abs_nonneg _
    have hx1 : 0 ≤ x₁ b := abs_nonneg _
    have hm0 : min (P₀ b) (P₁ b) ≤ P₀ b := min_le_left _ _
    have hm1 : min (P₀ b) (P₁ b) ≤ P₁ b := min_le_right _ _
    have hm : 0 ≤ min (P₀ b) (P₁ b) := le_min h0 h1
    nlinarith [mul_le_mul_of_nonneg_right hm0 hx0, mul_le_mul_of_nonneg_right hm1 hx1,
      mul_le_mul_of_nonneg_left htri hm]
  have hsummin : ∑ b, min (P₀ b) (P₁ b) = 1 - tvDist n p₀ p₁ := by
    have e : ∀ b, min (P₀ b) (P₁ b) = (P₀ b + P₁ b - |P₀ b - P₁ b|) / 2 := by
      intro b; rcases le_total (P₀ b) (P₁ b) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    simp_rw [e]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [hP₀, hP₁, sampleProb_sum, tvDist]
    ring
  have hTV : 0 ≤ 1 - tvDist n p₀ p₁ := by
    rw [← hsummin]; exact Finset.sum_nonneg (fun b _ => le_min (sampleProb_nonneg p₀ hp₀ b)
      (sampleProb_nonneg p₁ hp₁ b))
  have hreal : δ * (1 - tvDist n p₀ p₁) ≤
      (∑ b, P₀ b * x₀ b) + ∑ b, P₁ b * x₁ b := by
    rw [← Finset.sum_add_distrib]
    calc δ * (1 - tvDist n p₀ p₁) ≤ 2 * δ * (1 - tvDist n p₀ p₁) := by nlinarith
      _ = ∑ b, min (P₀ b) (P₁ b) * (2 * δ) := by rw [← Finset.sum_mul, hsummin]; ring
      _ ≤ _ := Finset.sum_le_sum (fun b _ => hmin b)
  -- 2 * target ≤ E₀ + E₁ ≤ 2 * sup
  have hS0 : 0 ≤ ∑ b, P₀ b * x₀ b :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (sampleProb_nonneg p₀ hp₀ b) (abs_nonneg _))
  have hS1 : 0 ≤ ∑ b, P₁ b * x₁ b :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (sampleProb_nonneg p₁ hp₁ b) (abs_nonneg _))
  have key : 2 * ENNReal.ofReal (δ / 2 * (1 - tvDist n p₀ p₁))
      ≤ 2 * ⨆ p ∈ Set.Icc (0 : ℝ) 1, estRisk k ρ M n R p := by
    calc 2 * ENNReal.ofReal (δ / 2 * (1 - tvDist n p₀ p₁))
        = ENNReal.ofReal (δ * (1 - tvDist n p₀ p₁)) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
      _ ≤ ENNReal.ofReal ((∑ b, P₀ b * x₀ b) + ∑ b, P₁ b * x₁ b) := ENNReal.ofReal_le_ofReal hreal
      _ = estRisk k ρ M n R p₀ + estRisk k ρ M n R p₁ := by
          rw [hE0, hE1, ENNReal.ofReal_add hS0 hS1]
      _ ≤ _ := by rw [two_mul]; exact add_le_add hsup0 hsup1
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp key
