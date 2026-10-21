-- Prove2me | solution 1 for VolunteerEngage.Thresholds.lemma_2_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:52:55.85321+00:00
-- url     : https://prove2.me/submissions/ea8f8cd9-1e3e-4a7f-a207-2526af5a76f7

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

lemma vet_Phi_sub_of_le (a b : ℝ) (hab : a ≤ b) :
    Cohen2019.Robust.Phi b - Cohen2019.Robust.Phi a =
      ∫ w in a..b, gaussianPDFReal 0 1 w := by
  have h := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at h
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero] at h
  have h1 : 0 ≤ ∫ w in Set.Ioc a b, gaussianPDFReal 0 1 w :=
    setIntegral_nonneg measurableSet_Ioc (fun w _ => gaussianPDFReal_nonneg _ _ _)
  have h2 : 0 ≤ Cohen2019.Robust.Phi b - Cohen2019.Robust.Phi a :=
    sub_nonneg.mpr ((monotone_cdf _) hab)
  have h3 := (ENNReal.ofReal_eq_ofReal_iff h1 h2).mp h
  rw [intervalIntegral.integral_of_le hab]
  unfold Cohen2019.Robust.Phi
  exact h3.symm

lemma vet_Phi_sub (a b : ℝ) :
    Cohen2019.Robust.Phi b - Cohen2019.Robust.Phi a =
      ∫ w in a..b, gaussianPDFReal 0 1 w := by
  rcases le_total a b with h | h
  · exact vet_Phi_sub_of_le a b h
  · rw [intervalIntegral.integral_symm, ← vet_Phi_sub_of_le b a h]; ring

lemma vet_gauss_int (a b : ℝ) :
    ∫ w in a..b, Real.exp (-w ^ 2 / 2) =
      Real.sqrt (2 * Real.pi) * (Cohen2019.Robust.Phi b - Cohen2019.Robust.Phi a) := by
  rw [vet_Phi_sub]
  have : ∀ w : ℝ, gaussianPDFReal 0 1 w = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-w ^ 2 / 2) := by
    intro w
    simp [gaussianPDFReal]
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]
  have : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

theorem vet_i (κ σ θ τ x : ℝ) (hκ : 0 < κ) (hσ : 0 < σ) :
    ∫ z in τ..x, Real.exp ((2 * θ * z - κ * z ^ 2) / σ ^ 2) =
      σ * Real.sqrt Real.pi / Real.sqrt κ * Real.exp (θ ^ 2 / (κ * σ ^ 2)) *
        (Cohen2019.Robust.Phi ((x - θ / κ) / (σ / Real.sqrt (2 * κ)))
          - Cohen2019.Robust.Phi ((τ - θ / κ) / (σ / Real.sqrt (2 * κ)))) := by
  set s := σ / Real.sqrt (2 * κ) with hs
  have h2κ : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.mpr (by positivity)
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs2 : s ^ 2 = σ ^ 2 / (2 * κ) := by
    rw [hs, div_pow, Real.sq_sqrt (by positivity)]
  have hpt : ∀ z : ℝ, Real.exp ((2 * θ * z - κ * z ^ 2) / σ ^ 2) =
      Real.exp (θ ^ 2 / (κ * σ ^ 2)) * Real.exp (-((z - θ / κ) / s) ^ 2 / 2) := by
    intro z
    rw [← Real.exp_add]
    congr 1
    rw [div_pow, hs2]
    field_simp
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  have e1 := intervalIntegral.integral_comp_sub_right
    (fun y : ℝ => Real.exp (-(y / s) ^ 2 / 2)) (a := τ) (b := x) (θ / κ)
  have e2 := intervalIntegral.integral_comp_div
    (fun w : ℝ => Real.exp (-w ^ 2 / 2)) (a := τ - θ / κ) (b := x - θ / κ) hs0.ne'
  rw [e1, e2, vet_gauss_int]
  have hk : Real.sqrt κ ≠ 0 := by positivity
  have hsq : s * Real.sqrt (2 * Real.pi) = σ * Real.sqrt Real.pi / Real.sqrt κ := by
    rw [hs, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  simp only [smul_eq_mul]
  rw [← hsq]
  ring

theorem solution (κ σ θ τ x : ℝ) (hκ : 0 < κ) (hσ : 0 < σ) :
    ∫ z in τ..x, Real.exp ((2 * θ * z - κ * z ^ 2) / σ ^ 2) =
      σ * Real.sqrt Real.pi / Real.sqrt κ * Real.exp (θ ^ 2 / (κ * σ ^ 2)) *
        (Cohen2019.Robust.Phi ((x - θ / κ) / (σ / Real.sqrt (2 * κ)))
          - Cohen2019.Robust.Phi ((τ - θ / κ) / (σ / Real.sqrt (2 * κ)))) :=
  vet_i κ σ θ τ x hκ hσ
