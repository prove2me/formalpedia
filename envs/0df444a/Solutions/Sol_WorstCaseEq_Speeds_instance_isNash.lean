-- Prove2me | solution 1 for WorstCaseEq.Speeds.instance_isNash
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:40:25.574984+00:00
-- url     : https://prove2.me/submissions/ddbd4559-cedc-42f3-8c7d-b6705baece62

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model
set_option autoImplicit false
open WorstCaseEq.Speeds

theorem gg_E (w s : Fin 2 → ℝ) (x y : Fin 2 → ℝ) (i : Fin 2) :
    AGT.expectedPayoff (S := fun _ : Fin 2 => Fin 2) (payoff w s) (![x, y] : Fin 2 → Fin 2 → ℝ) i =
      ∑ a0 : Fin 2, ∑ a1 : Fin 2, (x a0 * y a1) * payoff w s i (![a0, a1]) := by
  unfold AGT.expectedPayoff AGT.profileProb
  rw [← (Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm), Fintype.sum_prod_type]
  simp [Fin.prod_univ_two]

theorem gg_pay (w s : Fin 2 → ℝ) (a0 a1 : Fin 2) :
    payoff w s 0 (![a0, a1]) = -((w 0 + (if a1 = a0 then w 1 else 0)) / s a0) ∧
    payoff w s 1 (![a0, a1]) = -((w 1 + (if a0 = a1 then w 0 else 0)) / s a1) := by
  unfold payoff WorstCaseEq.Identical.load
  fin_cases a0 <;> fin_cases a1 <;>
    first
    | (simp [Finset.sum_filter, Fin.sum_univ_two, add_comm]; done)
    | (rw [Finset.sum_filter]; simp [Fin.sum_univ_two, add_comm]; done)
    | (simp [Finset.filter_insert, Finset.filter_singleton, Fin.univ_succ, Fin.sum_univ_two, add_comm]; done)
    | (decide)

theorem gg_E0 (w s : Fin 2 → ℝ) (x y : Fin 2 → ℝ) :
    AGT.expectedPayoff (S := fun _ : Fin 2 => Fin 2) (payoff w s) (![x, y] : Fin 2 → Fin 2 → ℝ) 0 =
      -(x 0 * (w 0 * (y 0 + y 1) + w 1 * y 0) / s 0 + x 1 * (w 0 * (y 0 + y 1) + w 1 * y 1) / s 1) := by
  rw [gg_E]
  simp only [Fin.sum_univ_two, (gg_pay _ _ _ _).1]
  simp
  ring

theorem gg_E1 (w s : Fin 2 → ℝ) (x y : Fin 2 → ℝ) :
    AGT.expectedPayoff (S := fun _ : Fin 2 => Fin 2) (payoff w s) (![x, y] : Fin 2 → Fin 2 → ℝ) 1 =
      -(y 0 * (w 1 * (x 0 + x 1) + w 0 * x 0) / s 0 + y 1 * (w 1 * (x 0 + x 1) + w 0 * x 1) / s 1) := by
  rw [gg_E]
  simp only [Fin.sum_univ_two, (gg_pay _ _ _ _).2]
  simp
  ring
theorem solution (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hφ : s₂ ≤ Real.goldenRatio * s₁) :
    IsNash (instWeights s₁ s₂) (speeds s₁ s₂) (instProfile s₁ s₂) := by
  have hs2 : 0 < s₂ := lt_of_lt_of_le h₁ h₁₂
  have hsum : 0 < s₁ + s₂ := by linarith
  have hg : s₂ ^ 2 ≤ s₁ * (s₁ + s₂) := by
    have h1 : (Real.goldenRatio * s₁) ^ 2 = (Real.goldenRatio + 1) * s₁ ^ 2 := by
      rw [mul_pow, Real.goldenRatio_sq]
    have h2 : 1 < Real.goldenRatio := Real.one_lt_goldenRatio
    have h3 : 0 ≤ s₂ + Real.goldenRatio * s₁ - s₁ := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hφ) h3]
  have hA0 : 0 ≤ s₁ ^ 2 / (s₂ * (s₁ + s₂)) := by positivity
  have hA1 : s₁ ^ 2 / (s₂ * (s₁ + s₂)) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hB0 : 0 ≤ s₂ ^ 2 / (s₁ * (s₁ + s₂)) := by positivity
  have hB1 : s₂ ^ 2 / (s₁ * (s₁ + s₂)) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  set A := s₁ ^ 2 / (s₂ * (s₁ + s₂)) with hA
  set B := s₂ ^ 2 / (s₁ * (s₁ + s₂)) with hB
  have hx : AGT.IsLottery (![A, 1 - A] : Fin 2 → ℝ) :=
    ⟨fun a => by fin_cases a <;> simp <;> linarith, by simp [Fin.sum_univ_two]⟩
  have hy : AGT.IsLottery (![1 - B, B] : Fin 2 → ℝ) :=
    ⟨fun a => by fin_cases a <;> simp <;> linarith, by simp [Fin.sum_univ_two]⟩
  have hprof : instProfile s₁ s₂ = ![![A, 1 - A], ![1 - B, B]] := rfl
  have c0 : (s₂ * ((1 - B) + B) + s₁ * (1 - B)) / s₁ = (s₁ + 2 * s₂) / (s₁ + s₂) := by
    rw [hB]; field_simp; ring
  have c1 : (s₂ * ((1 - B) + B) + s₁ * B) / s₂ = (s₁ + 2 * s₂) / (s₁ + s₂) := by
    rw [hB]; field_simp; ring
  have d0 : (s₁ * (A + (1 - A)) + s₂ * A) / s₁ = (2 * s₁ + s₂) / (s₁ + s₂) := by
    rw [hA]; field_simp; ring
  have d1 : (s₁ * (A + (1 - A)) + s₂ * (1 - A)) / s₂ = (2 * s₁ + s₂) / (s₁ + s₂) := by
    rw [hA]; field_simp; ring
  refine ⟨fun i => ?_, fun i τ hτ => ?_⟩
  · rw [hprof]; fin_cases i
    · exact hx
    · exact hy
  · rw [hprof]
    fin_cases i
    · have hu : Function.update (![![A, 1 - A], ![1 - B, B]] : Fin 2 → Fin 2 → ℝ) 0 τ
          = ![τ, ![1 - B, B]] := by
        funext j; fin_cases j <;> rfl
      simp only [Fin.zero_eta, hu]
      show AGT.expectedPayoff (S := fun _ : Fin 2 => Fin 2) (payoff (instWeights s₁ s₂) (speeds s₁ s₂))
          (![τ, ![1 - B, B]] : Fin 2 → Fin 2 → ℝ) 0 ≤ _
      rw [gg_E0, gg_E0]
      have hw0 : instWeights s₁ s₂ 0 = s₂ := rfl
      have hw1 : instWeights s₁ s₂ 1 = s₁ := rfl
      have hv0 : speeds s₁ s₂ 0 = s₁ := rfl
      have hv1 : speeds s₁ s₂ 1 = s₂ := rfl
      simp only [hw0, hw1, hv0, hv1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        mul_div_assoc, c0, c1]
      have hτ1 : τ 0 + τ 1 = 1 := by simpa [Fin.sum_univ_two] using hτ.2
      have key : ∀ C : ℝ, -(τ 0 * C + τ 1 * C) ≤ -(A * C + (1 - A) * C) := by
        intro C
        have e2 : τ 0 * C + τ 1 * C = C := by rw [← add_mul, hτ1, one_mul]
        rw [e2]; apply le_of_eq; ring
      exact key _
    · have hu : Function.update (![![A, 1 - A], ![1 - B, B]] : Fin 2 → Fin 2 → ℝ) 1 τ
          = ![![A, 1 - A], τ] := by
        funext j; fin_cases j <;> rfl
      simp only [Fin.mk_one, hu]
      show AGT.expectedPayoff (S := fun _ : Fin 2 => Fin 2) (payoff (instWeights s₁ s₂) (speeds s₁ s₂))
          (![![A, 1 - A], τ] : Fin 2 → Fin 2 → ℝ) 1 ≤ _
      rw [gg_E1, gg_E1]
      have hw0 : instWeights s₁ s₂ 0 = s₂ := rfl
      have hw1 : instWeights s₁ s₂ 1 = s₁ := rfl
      have hv0 : speeds s₁ s₂ 0 = s₁ := rfl
      have hv1 : speeds s₁ s₂ 1 = s₂ := rfl
      simp only [hw0, hw1, hv0, hv1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        mul_div_assoc, d0, d1]
      have hτ1 : τ 0 + τ 1 = 1 := by simpa [Fin.sum_univ_two] using hτ.2
      have key : ∀ C : ℝ, -(τ 0 * C + τ 1 * C) ≤ -((1 - B) * C + B * C) := by
        intro C
        have e2 : τ 0 * C + τ 1 * C = C := by rw [← add_mul, hτ1, one_mul]
        rw [e2]; apply le_of_eq; ring
      exact key _
