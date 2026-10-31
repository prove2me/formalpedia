-- Prove2me | solution 1 for TokenSignal.Asymmetry.low_type_indifference
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:24:46.525049+00:00
-- url     : https://prove2.me/submissions/0682395f-ea68-41fb-8836-590dfeca7d58

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model
open TokenSignal.Asymmetry

theorem solution(P : Params) (hS : P.Standing) :
    U P .L .H (αStar P) = U P .L .L 1 := by
  obtain ⟨hγ, hσ, hμ, hC, hI, hI2⟩ := hS
  have hER : ∀ j, ER P j = P.μ j / 4 := by
    intro j; unfold ER revLaw; rw [MeasureTheory.integral_div]; congr 1; exact ProbabilityTheory.integral_id_gaussianReal
  have hprob : MeasureTheory.IsProbabilityMeasure (revLaw P .L) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _
  have hmgf : ∀ t : ℝ, ∫ x, Real.exp (t * x) ∂revLaw P .L = Real.exp (P.μL * t + P.σ ^ 2 * t ^ 2 / 2) := by
    intro t
    have := congrFun (ProbabilityTheory.mgf_id_gaussianReal (μ := P.μ .L) (v := ⟨P.σ ^ 2, sq_nonneg _⟩)) t
    simp only [ProbabilityTheory.mgf, id] at this
    exact this
  have hU : ∀ (j : Ty) (α : ℝ), U P .L j α = P.γ⁻¹ - P.γ⁻¹ * Real.exp (-(P.γ * (α * ER P j - P.C - P.I))) * Real.exp (P.μL * (-(P.γ * (1 - α) / 4)) + P.σ ^ 2 * (-(P.γ * (1 - α) / 4)) ^ 2 / 2) := by
    intro j α
    unfold U
    have hi2 : MeasureTheory.Integrable (fun x => P.γ⁻¹ * Real.exp (-(P.γ * (α * ER P j - P.C - P.I))) * Real.exp ((-(P.γ * (1 - α) / 4)) * x)) (revLaw P .L) :=
      (ProbabilityTheory.integrable_exp_mul_gaussianReal _).const_mul _
    have hfun : (fun x => cara P.γ (α * ER P j + (1 - α) * (x / 4) - P.C - P.I)) = fun x => P.γ⁻¹ - (P.γ⁻¹ * Real.exp (-(P.γ * (α * ER P j - P.C - P.I)))) * Real.exp ((-(P.γ * (1 - α) / 4)) * x) := by
      funext x; unfold cara; rw [mul_assoc, ← Real.exp_add]; congr 3; ring
    rw [hfun, MeasureTheory.integral_sub (MeasureTheory.integrable_const _) hi2, MeasureTheory.integral_const, MeasureTheory.integral_const_mul, hmgf]
    simp
  rw [hU, hU, hER, hER]
  simp only [Params.μ]
  congr 1
  rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  set d := 4 * P.μH - 4 * P.μL with hd
  have hd0 : 0 < d := by linarith
  have hs : 0 < P.σ ^ 2 * P.γ := by positivity
  have h0 : 0 ≤ d * (d + 2 * P.σ ^ 2 * P.γ) := by positivity
  have hR := Real.sq_sqrt h0
  have has : αStar P * (P.σ ^ 2 * P.γ) = d + P.σ ^ 2 * P.γ - Real.sqrt (d * (d + 2 * P.σ ^ 2 * P.γ)) := by
    unfold αStar; rw [← hd]; field_simp
  set R := Real.sqrt (d * (d + 2 * P.σ ^ 2 * P.γ)) with hRdef
  clear_value R
  set a := αStar P with ha
  clear_value a
  have key : (P.σ ^ 2 * P.γ) * ((P.σ ^ 2 * P.γ) * (1 - a) ^ 2 - 2 * d * a) = 0 := by
    first
    | linear_combination hR + (a * (P.σ ^ 2 * P.γ) - d - P.σ ^ 2 * P.γ - R) * has
    | linear_combination -hR - (a * (P.σ ^ 2 * P.γ) - d - P.σ ^ 2 * P.γ - R) * has
    | linear_combination hR - (a * (P.σ ^ 2 * P.γ) - d - P.σ ^ 2 * P.γ - R) * has
    | linear_combination -hR + (a * (P.σ ^ 2 * P.γ) - d - P.σ ^ 2 * P.γ - R) * has
  have key2 : (P.σ ^ 2 * P.γ) * (1 - a) ^ 2 = 2 * d * a := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hs.ne'
    · linarith
  linear_combination (P.γ / 32) * key2
