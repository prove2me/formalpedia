-- Prove2me | solution 1 for PriceQualityService.Uniform.equation_24
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:28:21.055925+00:00
-- url     : https://prove2.me/submissions/8230c126-f9ac-468c-bc18-e65097c4e7fd

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model
import Definitions.Def_PriceQualityService_Uniform_Reduction

set_option autoImplicit false
open PriceQualityService.Uniform Finset

theorem gTerm_eq' {N : ℕ} (α a b c s : Fin N → ℝ) (r t : ℝ) (i : Fin N) :
    gTerm α a b c s r t i = Real.exp (exponent α a b c s t i) / Real.exp (1 + r) := by
  unfold gTerm
  rw [← Real.exp_sub]; congr 1; ring

theorem sum_gTerm' {N : ℕ} (α a b c s : Fin N → ℝ) (r t : ℝ) :
    ∑ i, gTerm α a b c s r t i = yTotal α a b c s t / Real.exp (1 + r) := by
  simp_rw [gTerm_eq']
  rw [← Finset.sum_div]; rfl

theorem yTotal_nonneg' {N : ℕ} (α a b c s : Fin N → ℝ) (t : ℝ) : 0 ≤ yTotal α a b c s t :=
  Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)

theorem per_i' (u m φ r : ℝ) (h : m ≤ φ - u) :
    m * Real.exp u ≤ Real.exp (φ - r - 1) + r * Real.exp u := by
  have hu := Real.exp_pos u
  have h1 : m * Real.exp u ≤ (φ - u) * Real.exp u := mul_le_mul_of_nonneg_right h hu.le
  have h2 : (φ - r - 1) - u + 1 ≤ Real.exp ((φ - r - 1) - u) := Real.add_one_le_exp _
  have h3 : Real.exp (φ - r - 1) = Real.exp u * Real.exp ((φ - r - 1) - u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp u * ((φ - r - 1) - u + 1) ≤ Real.exp (φ - r - 1) := by
    rw [h3]; exact mul_le_mul_of_nonneg_left h2 hu.le
  nlinarith

theorem root_exists' {N : ℕ} (α a b c s : Fin N → ℝ) (t : ℝ) :
    ∃ r : ℝ, r = ∑ i, gTerm α a b c s r t i := by
  set Y := yTotal α a b c s t with hY
  have hY0 : 0 ≤ Y := yTotal_nonneg' α a b c s t
  have hcont : ContinuousOn (fun r : ℝ => r * Real.exp (1 + r)) (Set.Icc 0 Y) := by
    fun_prop
  have h0 : (fun r : ℝ => r * Real.exp (1 + r)) 0 ≤ Y := by simp [hY0]
  have h1 : Y ≤ (fun r : ℝ => r * Real.exp (1 + r)) Y := by
    show Y ≤ Y * Real.exp (1 + Y)
    have : 1 ≤ Real.exp (1 + Y) := Real.one_le_exp (by linarith)
    nlinarith
  obtain ⟨r, _, hr⟩ := intermediate_value_Icc hY0 hcont ⟨h0, h1⟩
  refine ⟨r, ?_⟩
  rw [sum_gTerm', eq_div_iff (Real.exp_pos _).ne']
  exact hr

theorem root_unique' {N : ℕ} (α a b c s : Fin N → ℝ) (t : ℝ) (r r' : ℝ)
    (h : r = ∑ i, gTerm α a b c s r t i) (h' : r' = ∑ i, gTerm α a b c s r' t i) : r = r' := by
  rw [sum_gTerm'] at h h'
  have hY0 := yTotal_nonneg' α a b c s t
  have hr0 : 0 ≤ r := by rw [h]; exact div_nonneg hY0 (Real.exp_pos _).le
  have hr0' : 0 ≤ r' := by rw [h']; exact div_nonneg hY0 (Real.exp_pos _).le
  have e1 : r * Real.exp (1 + r) = yTotal α a b c s t := (eq_div_iff (Real.exp_pos _).ne').1 h
  have e2 : r' * Real.exp (1 + r') = yTotal α a b c s t := (eq_div_iff (Real.exp_pos _).ne').1 h'
  have hmono : ∀ x y : ℝ, 0 ≤ x → x < y → x * Real.exp (1 + x) < y * Real.exp (1 + y) := by
    intro x y hx hxy
    have h1 : Real.exp (1 + x) ≤ Real.exp (1 + y) := Real.exp_le_exp.2 (by linarith)
    have h2 := Real.exp_pos (1 + y)
    calc x * Real.exp (1 + x) ≤ x * Real.exp (1 + y) := mul_le_mul_of_nonneg_left h1 hx
      _ < y * Real.exp (1 + y) := mul_lt_mul_of_pos_right hxy h2
  rcases lt_trichotomy r r' with hlt | heq | hgt
  · have := hmono _ _ hr0 hlt; linarith
  · exact heq
  · have := hmono _ _ hr0' hgt; linarith

theorem exponent_sub' {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (t : ℝ) (i : Fin N)
    (q : ℝ) : exponent α a b c s t i - (-(c i) * q ^ 2 + (α i + t * b i) * q + t * (s i - a i))
      = c i * (q - (α i + t * b i) / (2 * c i)) ^ 2 := by
  have := (hc i).ne'
  unfold exponent
  field_simp
  ring

theorem profit_le' {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (t r : ℝ)
    (hr : r = ∑ i, gTerm α a b c s r t i) (p q : Fin N → ℝ) :
    PriceQualityService.Joint.profit α a b c s p q (fun _ => t) ≤ r := by
  set e : Fin N → ℝ := fun i => Real.exp (α i * q i - p i + t * s i) with he
  have hepos : ∀ i, 0 < e i := fun i => Real.exp_pos _
  set S := ∑ i, e i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => (hepos i).le)
  have hD : 0 < 1 + S := by linarith
  have hprofit : PriceQualityService.Joint.profit α a b c s p q (fun _ => t) =
      (∑ i, PriceQualityService.Joint.markup a b c p q (fun _ => t) i * e i) / (1 + S) := by
    unfold PriceQualityService.Joint.profit PriceQualityService.Joint.choiceProb
      PriceQualityService.Joint.attraction
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_div_assoc]
  rw [hprofit, div_le_iff₀ hD]
  have hper : ∀ i, PriceQualityService.Joint.markup a b c p q (fun _ => t) i * e i ≤
      gTerm α a b c s r t i + r * e i := by
    intro i
    have hm : PriceQualityService.Joint.markup a b c p q (fun _ => t) i ≤
        exponent α a b c s t i - (α i * q i - p i + t * s i) := by
      have h := exponent_sub' α a b c s hc t i (q i)
      have hnn : 0 ≤ c i * (q i - (α i + t * b i) / (2 * c i)) ^ 2 :=
        mul_nonneg (hc i).le (sq_nonneg _)
      unfold PriceQualityService.Joint.markup
      nlinarith [h, hnn]
    exact per_i' (α i * q i - p i + t * s i) _ _ r hm
  calc ∑ i, PriceQualityService.Joint.markup a b c p q (fun _ => t) i * e i
      ≤ ∑ i, (gTerm α a b c s r t i + r * e i) := Finset.sum_le_sum (fun i _ => hper i)
    _ = r + r * S := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hr]
    _ = r * (1 + S) := by ring

theorem profit_attained' {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (t r : ℝ)
    (hr : r = ∑ i, gTerm α a b c s r t i) :
    PriceQualityService.Joint.profit α a b c s
        (fun i => 1 + r + c i * ((α i + t * b i) / (2 * c i)) ^ 2
          + t * (a i - b i * ((α i + t * b i) / (2 * c i))))
        (fun i => (α i + t * b i) / (2 * c i)) (fun _ => t) = r := by
  have hr0 : 0 ≤ r := by
    rw [hr]; exact Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  have hG : ∀ i, PriceQualityService.Joint.attraction α s
        (fun i => 1 + r + c i * ((α i + t * b i) / (2 * c i)) ^ 2
          + t * (a i - b i * ((α i + t * b i) / (2 * c i))))
        (fun i => (α i + t * b i) / (2 * c i)) (fun _ => t) i = gTerm α a b c s r t i := by
    intro i
    unfold PriceQualityService.Joint.attraction gTerm
    congr 1
    have h := exponent_sub' α a b c s hc t i ((α i + t * b i) / (2 * c i))
    have h0 : c i * ((α i + t * b i) / (2 * c i) - (α i + t * b i) / (2 * c i)) ^ 2 = 0 := by simp
    simp only [sub_self] at h
    nlinarith [h]
  have hm : ∀ i, PriceQualityService.Joint.markup a b c
        (fun i => 1 + r + c i * ((α i + t * b i) / (2 * c i)) ^ 2
          + t * (a i - b i * ((α i + t * b i) / (2 * c i))))
        (fun i => (α i + t * b i) / (2 * c i)) (fun _ => t) i = 1 + r := by
    intro i
    unfold PriceQualityService.Joint.markup
    ring
  unfold PriceQualityService.Joint.profit PriceQualityService.Joint.choiceProb
  simp only [hm, hG]
  rw [← hr]
  have h1 : (1 + r) ≠ 0 := by linarith
  have : ∀ i, (1 + r) * (gTerm α a b c s r t i / (1 + r)) = gTerm α a b c s r t i := by
    intro i; field_simp
  simp_rw [this]
  exact hr.symm

theorem solution {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (t : ℝ) :
    (∃! r : ℝ, r = ∑ i, gTerm α a b c s r t i) ∧
    ∀ r : ℝ, r = ∑ i, gTerm α a b c s r t i →
      (∀ p q : Fin N → ℝ, PriceQualityService.Joint.profit α a b c s p q (fun _ => t) ≤ r) ∧
      PriceQualityService.Joint.profit α a b c s
        (fun i => 1 + r + c i * ((α i + t * b i) / (2 * c i)) ^ 2
          + t * (a i - b i * ((α i + t * b i) / (2 * c i))))
        (fun i => (α i + t * b i) / (2 * c i)) (fun _ => t) = r := by
  refine ⟨?_, fun r hr => ⟨fun p q => profit_le' α a b c s hc t r hr p q,
    profit_attained' α a b c s hc t r hr⟩⟩
  obtain ⟨r, hr⟩ := root_exists' α a b c s t
  exact ⟨r, hr, fun r' hr' => (root_unique' α a b c s t r r' hr hr').symm⟩
