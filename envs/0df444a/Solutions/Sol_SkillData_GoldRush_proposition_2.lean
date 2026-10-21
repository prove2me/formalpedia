-- Prove2me | solution 1 for SkillData.GoldRush.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T01:36:32.549513+00:00
-- url     : https://prove2.me/submissions/62fe4b1a-00e4-42c9-a71c-c2a7dfe9823e

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model
import Theorems.Thm_SkillData_GoldRush_unique_pair_of_clarity
import Theorems.Thm_SkillData_GoldRush_eq_C5

open SkillData.GoldRush Filter Topology

namespace GRUpair

lemma cv_eq (P : Params) (τη prec : ℝ) :
    condVar P τη prec = 1 / (P.τθ + τη) + (τη / (P.τθ + τη)) ^ 2 / (P.τθ * τη / (P.τθ + τη) + prec) := by
  unfold condVar; ring

lemma cv_pos (P : Params) (τη prec : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hp : 0 ≤ prec) :
    0 < condVar P τη prec := by
  rw [cv_eq]; positivity

lemma cv_ge (P : Params) (τη prec : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hp : 0 ≤ prec) :
    1 / (P.τθ + τη) ≤ condVar P τη prec := by
  rw [cv_eq]
  have : 0 ≤ (τη / (P.τθ + τη)) ^ 2 / (P.τθ * τη / (P.τθ + τη) + prec) := by positivity
  linarith

lemma cv_anti (P : Params) (τη p q : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hp : 0 ≤ p) (hpq : p < q) :
    condVar P τη q < condVar P τη p := by
  rw [cv_eq, cv_eq]
  have hk : 0 < P.τθ * τη / (P.τθ + τη) := by positivity
  have : (τη / (P.τθ + τη)) ^ 2 / (P.τθ * τη / (P.τθ + τη) + q)
      < (τη / (P.τθ + τη)) ^ 2 / (P.τθ * τη / (P.τθ + τη) + p) := by
    apply div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  linarith

/-- the ratio condVar(p+z)/condVar(p) is strictly increasing in p ≥ 0 when z > 0 -/
lemma cv_ratio_mono (P : Params) (τη p q z : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hp : 0 ≤ p)
    (hpq : p < q) (hz : 0 < z) :
    condVar P τη (p + z) / condVar P τη p < condVar P τη (q + z) / condVar P τη q := by
  have hq : 0 ≤ q := by linarith
  rw [div_lt_div_iff₀ (cv_pos P τη p hθ hτ hp) (cv_pos P τη q hθ hτ hq)]
  rw [cv_eq, cv_eq, cv_eq, cv_eq]
  set a := 1 / (P.τθ + τη) with ha
  set b := (τη / (P.τθ + τη)) ^ 2 with hb
  set k := P.τθ * τη / (P.τθ + τη) with hk
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hk0 : 0 < k := by positivity
  clear_value a b k
  set m := k + p
  set M := k + q
  have hm : 0 < m := by positivity
  have hmM : m < M := by simp only [m, M]; linarith
  have e1 : k + (p + z) = m + z := by simp only [m]; ring
  have e2 : k + (q + z) = M + z := by simp only [M]; ring
  rw [e1, e2]
  have hM : 0 < M := by linarith
  have l1 : a + b / (m + z) = (a * (m + z) + b) / (m + z) := by field_simp
  have l2 : a + b / M = (a * M + b) / M := by field_simp
  have l3 : a + b / (M + z) = (a * (M + z) + b) / (M + z) := by field_simp
  have l4 : a + b / m = (a * m + b) / m := by field_simp
  rw [l1, l2, l3, l4, div_mul_div_comm, div_mul_div_comm,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have key : (a * (M + z) + b) * (a * m + b) * ((m + z) * M) - (a * (m + z) + b) * (a * M + b) * ((M + z) * m)
      = b * z * (M - m) * (M * a + a * m + a * z + b) := by ring
  have : 0 < b * z * (M - m) * (M * a + a * m + a * z + b) := by
    have : 0 < M - m := by linarith
    positivity
  nlinarith

lemma cv_cont (P : Params) (τη z : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu) (hz : 0 ≤ z) :
    Continuous fun α : ℝ => condVar P τη (α ^ 2 * P.τu + z) := by
  have : (fun α : ℝ => condVar P τη (α ^ 2 * P.τu + z)) = fun α =>
      1 / (P.τθ + τη) + (τη / (P.τθ + τη)) ^ 2 / (P.τθ * τη / (P.τθ + τη) + (α ^ 2 * P.τu + z)) := by
    funext α; rw [cv_eq]
  rw [this]
  apply Continuous.add continuous_const
  apply Continuous.div continuous_const (by fun_prop)
  intro α; positivity


lemma cv_anti_le (P : Params) (τη p q : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hp : 0 ≤ p) (hpq : p ≤ q) :
    condVar P τη q ≤ condVar P τη p := by
  rcases eq_or_lt_of_le hpq with h | h
  · rw [h]
  · exact (cv_anti P τη p q hθ hτ hp h).le

lemma gain_eq (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hxH : 0 ≤ x * P.ZH) (hxL : 0 ≤ x * P.ZL) :
    gain P τη x α = -(1 / P.γ) * Real.log (1 / 2 * Real.sqrt (varH P τη x α / varU P τη α)
      + 1 / 2 * Real.sqrt (varL P τη x α / varU P τη α)) := by
  have hU := cv_pos P τη (α ^ 2 * P.τu) hθ hτ (by positivity)
  have hH := cv_pos P τη (α ^ 2 * P.τu + x * P.ZH) hθ hτ (by positivity)
  have hL := cv_pos P τη (α ^ 2 * P.τu + x * P.ZL) hθ hτ (by positivity)
  unfold gain
  simp only [varU, varH, varL] at *
  rw [Real.sqrt_div' _ hU.le, Real.sqrt_div' _ hU.le]
  have hsU : 0 < Real.sqrt (condVar P τη (α ^ 2 * P.τu)) := Real.sqrt_pos.mpr hU
  have hsH : 0 < Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZH)) := Real.sqrt_pos.mpr hH
  have hsL : 0 < Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZL)) := Real.sqrt_pos.mpr hL
  have : 1 / 2 * (Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZH)) / Real.sqrt (condVar P τη (α ^ 2 * P.τu)))
      + 1 / 2 * (Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZL)) / Real.sqrt (condVar P τη (α ^ 2 * P.τu)))
      = (Real.sqrt (condVar P τη (α ^ 2 * P.τu)) / (1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZH))
        + 1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZL))))⁻¹ := by
    field_simp
  rw [this, Real.log_inv]; ring

lemma gain_strictAnti (P : Params) (τη x α β : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hγ : 0 < P.γ) (hxH : 0 < x * P.ZH) (hxL : 0 < x * P.ZL) (hα : 0 ≤ α) (hαβ : α < β) :
    gain P τη x β < gain P τη x α := by
  rw [gain_eq P τη x α hθ hτ hu hxH.le hxL.le, gain_eq P τη x β hθ hτ hu hxH.le hxL.le]
  have hp : α ^ 2 * P.τu < β ^ 2 * P.τu := by
    apply mul_lt_mul_of_pos_right _ hu; nlinarith
  have hp0 : 0 ≤ α ^ 2 * P.τu := by positivity
  have r1 := cv_ratio_mono P τη _ _ _ hθ hτ hp0 hp hxH
  have r2 := cv_ratio_mono P τη _ _ _ hθ hτ hp0 hp hxL
  simp only [varU, varH, varL]
  have hpos1 : 0 < condVar P τη (α ^ 2 * P.τu + x * P.ZH) / condVar P τη (α ^ 2 * P.τu) :=
    div_pos (cv_pos _ _ _ hθ hτ (by positivity)) (cv_pos _ _ _ hθ hτ hp0)
  have s1 := Real.sqrt_lt_sqrt hpos1.le r1
  have s2 := Real.sqrt_lt_sqrt (div_pos (cv_pos _ _ _ hθ hτ (by positivity)) (cv_pos _ _ _ hθ hτ hp0)).le r2
  have hA : 0 < 1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZH) / condVar P τη (α ^ 2 * P.τu))
      + 1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZL) / condVar P τη (α ^ 2 * P.τu)) := by
    have := Real.sqrt_pos.mpr hpos1
    positivity
  have hlog := Real.log_lt_log hA (by linarith : 1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZH) / condVar P τη (α ^ 2 * P.τu))
      + 1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZL) / condVar P τη (α ^ 2 * P.τu)) <
      1 / 2 * Real.sqrt (condVar P τη (β ^ 2 * P.τu + x * P.ZH) / condVar P τη (β ^ 2 * P.τu))
      + 1 / 2 * Real.sqrt (condVar P τη (β ^ 2 * P.τu + x * P.ZL) / condVar P τη (β ^ 2 * P.τu)))
  have : 0 < 1 / P.γ := by positivity
  nlinarith

lemma gain_pos (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hγ : 0 < P.γ) (hxH : 0 < x * P.ZH) (hxL : 0 < x * P.ZL) :
    0 < gain P τη x α := by
  rw [gain_eq P τη x α hθ hτ hu hxH.le hxL.le]
  simp only [varU, varH, varL]
  have hp0 : 0 ≤ α ^ 2 * P.τu := by positivity
  have hU := cv_pos P τη _ hθ hτ hp0
  have r1 : condVar P τη (α ^ 2 * P.τu + x * P.ZH) / condVar P τη (α ^ 2 * P.τu) < 1 := by
    rw [div_lt_one hU]; exact cv_anti _ _ _ _ hθ hτ hp0 (by linarith)
  have r2 : condVar P τη (α ^ 2 * P.τu + x * P.ZL) / condVar P τη (α ^ 2 * P.τu) < 1 := by
    rw [div_lt_one hU]; exact cv_anti _ _ _ _ hθ hτ hp0 (by linarith)
  have q1 : 0 < condVar P τη (α ^ 2 * P.τu + x * P.ZH) / condVar P τη (α ^ 2 * P.τu) :=
    div_pos (cv_pos _ _ _ hθ hτ (by positivity)) hU
  have s1 : Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZH) / condVar P τη (α ^ 2 * P.τu)) < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using r1
  have s2 : Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZL) / condVar P τη (α ^ 2 * P.τu)) < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using r2
  have hA : 0 < 1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZH) / condVar P τη (α ^ 2 * P.τu))
      + 1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZL) / condVar P τη (α ^ 2 * P.τu)) := by
    have := Real.sqrt_pos.mpr q1
    positivity
  have hlog := Real.log_neg hA (by linarith)
  have : 0 < 1 / P.γ := by positivity
  nlinarith

lemma gain_le (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hγ : 0 < P.γ) (hxH : 0 ≤ x * P.ZH) (hxL : 0 ≤ x * P.ZL) :
    gain P τη x α ≤ 1 / P.γ * Real.log (Real.sqrt (condVar P τη 0) / Real.sqrt (1 / (P.τθ + τη))) := by
  unfold gain
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hp0 : 0 ≤ α ^ 2 * P.τu := by positivity
  have hA0 : 0 < 1 / (P.τθ + τη) := by positivity
  have hsA : 0 < Real.sqrt (1 / (P.τθ + τη)) := Real.sqrt_pos.mpr hA0
  have hH := cv_ge P τη (α ^ 2 * P.τu + x * P.ZH) hθ hτ (by positivity)
  have hL := cv_ge P τη (α ^ 2 * P.τu + x * P.ZL) hθ hτ (by positivity)
  have hU := cv_pos P τη _ hθ hτ hp0
  have hU0 := cv_anti_le P τη 0 _ hθ hτ le_rfl hp0
  have sH := Real.sqrt_le_sqrt hH
  have sL := Real.sqrt_le_sqrt hL
  have sU := Real.sqrt_le_sqrt hU0
  have hsU : 0 < Real.sqrt (varU P τη α) := Real.sqrt_pos.mpr hU
  have hden : 0 < 1 / 2 * Real.sqrt (varH P τη x α) + 1 / 2 * Real.sqrt (varL P τη x α) := by
    have := Real.sqrt_pos.mpr (cv_pos P τη (α ^ 2 * P.τu + x * P.ZH) hθ hτ (by positivity))
    have := Real.sqrt_nonneg (condVar P τη (α ^ 2 * P.τu + x * P.ZL))
    simp only [varH, varL]; positivity
  apply Real.log_le_log
  · exact div_pos hsU hden
  · rw [div_le_div_iff₀ hden hsA]
    simp only [varH, varL, varU] at *
    have h1 : Real.sqrt (condVar P τη (α ^ 2 * P.τu)) * Real.sqrt (1 / (P.τθ + τη)) ≤
        Real.sqrt (condVar P τη 0) * Real.sqrt (1 / (P.τθ + τη)) :=
      mul_le_mul_of_nonneg_right sU hsA.le
    have h2 : Real.sqrt (condVar P τη 0) * Real.sqrt (1 / (P.τθ + τη)) ≤ Real.sqrt (condVar P τη 0) *
        (1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZH)) +
          1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZL))) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    linarith

lemma gain_cont (P : Params) (τη x : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hxH : 0 ≤ x * P.ZH) (hxL : 0 ≤ x * P.ZL) :
    Continuous fun α => gain P τη x α := by
  unfold gain varU varH varL
  have cU := cv_cont P τη 0 hθ hτ hu le_rfl
  simp only [add_zero] at cU
  have cH := cv_cont P τη _ hθ hτ hu hxH
  have cL := cv_cont P τη _ hθ hτ hu hxL
  apply Continuous.mul continuous_const
  apply Continuous.log
  · apply Continuous.div (Real.continuous_sqrt.comp cU)
    · exact ((Real.continuous_sqrt.comp cH).const_smul (1/2 : ℝ)).add ((Real.continuous_sqrt.comp cL).const_smul (1/2 : ℝ)) |>.congr (fun α => by simp [smul_eq_mul])
    · intro α
      have := Real.sqrt_pos.mpr (cv_pos P τη (α ^ 2 * P.τu + x * P.ZH) hθ hτ (by positivity))
      have := Real.sqrt_nonneg (condVar P τη (α ^ 2 * P.τu + x * P.ZL))
      positivity
  · intro α
    have := Real.sqrt_pos.mpr (cv_pos P τη (α ^ 2 * P.τu + x * P.ZH) hθ hτ (by positivity))
    have := Real.sqrt_nonneg (condVar P τη (α ^ 2 * P.τu + x * P.ZL))
    have := Real.sqrt_pos.mpr (cv_pos P τη (α ^ 2 * P.τu) hθ hτ (by positivity))
    positivity


/-- the mass `λ` that solves (14) given `(x, α)` -/
noncomputable def lamOf (P : Params) (τη x α : ℝ) : ℝ :=
  2 * P.γ * α * (x * P.ZH + (P.τu * α ^ 2 + τη)) * (x * P.ZL + (P.τu * α ^ 2 + τη)) /
    (τη * ((P.τu * α ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL)))

lemma eq14_iff (P : Params) (τη x lam α : ℝ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hxH : 0 < x * P.ZH) (hxL : 0 < x * P.ZL) :
    Eq14 P τη x lam α ↔ lam = lamOf P τη x α := by
  have hupos : 0 < P.τu * α ^ 2 + τη := by positivity
  have hD : 0 < (P.τu * α ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL) := by
    positivity
  have hbu : 0 < x * P.ZL + P.τu * α ^ 2 + τη := by positivity
  have hid : P.γ * α * (x * P.ZH + P.τu * α ^ 2 + τη)
      - 1 / 2 * x * lam * τη *
        (P.ZH + P.ZL + x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + P.τu * α ^ 2 + τη))
      = τη * ((P.τu * α ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL))
          / (2 * (x * P.ZL + P.τu * α ^ 2 + τη)) * (lamOf P τη x α - lam) := by
    unfold lamOf
    have h4 : x * P.ZL + (P.τu * α ^ 2 + τη) ≠ 0 := by rw [← add_assoc]; exact hbu.ne'
    have e1 : x * (P.ZH + P.ZL + x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + P.τu * α ^ 2 + τη))
        = ((P.τu * α ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL))
          / (x * P.ZL + P.τu * α ^ 2 + τη) := by
      rw [eq_div_iff hbu.ne']
      field_simp
      ring
    have e2 : τη * ((P.τu * α ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL))
          / (2 * (x * P.ZL + P.τu * α ^ 2 + τη)) *
        (2 * P.γ * α * (x * P.ZH + (P.τu * α ^ 2 + τη)) * (x * P.ZL + (P.τu * α ^ 2 + τη)) /
          (τη * ((P.τu * α ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL))))
        = P.γ * α * (x * P.ZH + P.τu * α ^ 2 + τη) := by
      have h1 := hD.ne'
      have h3 := hτ.ne'
      rw [div_mul_div_comm, div_eq_iff (by positivity)]
      ring
    calc _ = P.γ * α * (x * P.ZH + P.τu * α ^ 2 + τη) - 1 / 2 * lam * τη *
          (x * (P.ZH + P.ZL + x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + P.τu * α ^ 2 + τη))) := by ring
      _ = _ := by
        rw [e1, mul_sub, e2, mul_comm 2 (x * P.ZL + P.τu * α ^ 2 + τη), ← div_div]
        ring
  unfold Eq14
  rw [hid]
  have hK : τη * ((P.τu * α ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL))
          / (2 * (x * P.ZL + P.τu * α ^ 2 + τη)) ≠ 0 := by positivity
  rw [mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hK
    · exact h.symm
  · intro h; right; exact h.symm

lemma ND_mono (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) (huv : u < v) :
    (a + u) * (b + u) / (u * (a + b) + 2 * a * b) < (a + v) * (b + v) / (v * (a + b) + 2 * a * b) := by
  have hv : 0 < v := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have key : (a + v) * (b + v) * (u * (a + b) + 2 * a * b) - (a + u) * (b + u) * (v * (a + b) + 2 * a * b)
      = (v - u) * (a * b * (a + b) + 2 * (a * b) * u + 2 * (a * b) * v + (a + b) * u * v) := by ring
  have : 0 < (v - u) * (a * b * (a + b) + 2 * (a * b) * u + 2 * (a * b) * v + (a + b) * u * v) := by
    have : 0 < v - u := by linarith
    positivity
  linarith

lemma lamOf_eq (P : Params) (τη x α : ℝ) :
    lamOf P τη x α = 2 * P.γ / τη * α * ((x * P.ZH + (P.τu * α ^ 2 + τη)) * (x * P.ZL + (P.τu * α ^ 2 + τη)) /
      ((P.τu * α ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL))) := by
  unfold lamOf; simp only [div_eq_mul_inv, mul_inv]; ring

lemma lamOf_strictMono (P : Params) (τη x α β : ℝ) (hτ : 0 < τη) (hu : 0 < P.τu) (hγ : 0 < P.γ)
    (hxH : 0 < x * P.ZH) (hxL : 0 < x * P.ZL) (hα : 0 ≤ α) (hαβ : α < β) :
    lamOf P τη x α < lamOf P τη x β := by
  rw [lamOf_eq, lamOf_eq]
  have hu1 : 0 < P.τu * α ^ 2 + τη := by positivity
  have hu12 : P.τu * α ^ 2 + τη < P.τu * β ^ 2 + τη := by
    have : α ^ 2 < β ^ 2 := by nlinarith
    nlinarith
  have h := ND_mono (x * P.ZH) (x * P.ZL) _ _ hxH hxL hu1 hu12
  have e : ∀ w : ℝ, (x * P.ZH + w) * (x * P.ZL + w) / (w * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL))
      = (x * P.ZH + w) * (x * P.ZL + w) / (w * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL)) := fun _ => rfl
  have hc : 0 < 2 * P.γ / τη := by positivity
  have g2 : 0 < (x * P.ZH + (P.τu * β ^ 2 + τη)) * (x * P.ZL + (P.τu * β ^ 2 + τη)) /
      ((P.τu * β ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL)) := by
    have : 0 < P.τu * β ^ 2 + τη := by positivity
    positivity
  have h' : (x * P.ZH + (P.τu * α ^ 2 + τη)) * (x * P.ZL + (P.τu * α ^ 2 + τη)) /
      ((P.τu * α ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL)) <
      (x * P.ZH + (P.τu * β ^ 2 + τη)) * (x * P.ZL + (P.τu * β ^ 2 + τη)) /
      ((P.τu * β ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL)) := by
    convert h using 2
  have g1 : 0 ≤ (x * P.ZH + (P.τu * α ^ 2 + τη)) * (x * P.ZL + (P.τu * α ^ 2 + τη)) /
      ((P.τu * α ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL)) := by positivity
  have hb : 0 < β := by linarith
  calc 2 * P.γ / τη * α * _ ≤ 2 * P.γ / τη * α * ((x * P.ZH + (P.τu * β ^ 2 + τη)) * (x * P.ZL + (P.τu * β ^ 2 + τη)) /
      ((P.τu * β ^ 2 + τη) * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL))) := by
        apply mul_le_mul_of_nonneg_left h'.le (by positivity)
    _ < _ := by
        apply mul_lt_mul_of_pos_right _ g2
        exact mul_lt_mul_of_pos_left hαβ hc

lemma lamOf_cont (P : Params) (τη x : ℝ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hxH : 0 < x * P.ZH) (hxL : 0 < x * P.ZL) : Continuous fun α => lamOf P τη x α := by
  unfold lamOf
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro α
  have : 0 < P.τu * α ^ 2 + τη := by positivity
  positivity

lemma lamOf_pos (P : Params) (τη x α : ℝ) (hτ : 0 < τη) (hu : 0 < P.τu) (hγ : 0 < P.γ)
    (hxH : 0 < x * P.ZH) (hxL : 0 < x * P.ZL) (hα : 0 < α) : 0 < lamOf P τη x α := by
  unfold lamOf
  have : 0 < P.τu * α ^ 2 + τη := by positivity
  positivity

lemma lamOf_gt (P : Params) (τη x α : ℝ) (hτ : 0 < τη) (hu : 0 < P.τu) (hγ : 0 < P.γ)
    (hxH : 0 < x * P.ZH) (hxL : 0 < x * P.ZL) (hα : 0 < α) : P.γ * α / τη < lamOf P τη x α := by
  rw [lamOf_eq]
  have hw : 0 < P.τu * α ^ 2 + τη := by positivity
  set w := P.τu * α ^ 2 + τη
  have hD : 0 < w * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL) := by positivity
  have h2 : 1 / 2 < (x * P.ZH + w) * (x * P.ZL + w) / (w * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL)) := by
    rw [lt_div_iff₀ hD]
    nlinarith [mul_pos hw hw, mul_pos hw (add_pos hxH hxL)]
  have : 0 < 2 * P.γ / τη * α := by positivity
  calc P.γ * α / τη = 2 * P.γ / τη * α * (1 / 2) := by field_simp
    _ < _ := mul_lt_mul_of_pos_left h2 this



/-! ### Reparametrization by `s = 1/x`, with `s = 0` the "as is" clarity -/

noncomputable def Vs (P : Params) (τη s p Z : ℝ) : ℝ :=
  1 / (P.τθ + τη) + (τη / (P.τθ + τη)) ^ 2 * s / (s * (P.τθ * τη / (P.τθ + τη) + p) + Z)

noncomputable def Gs (P : Params) (τη s α : ℝ) : ℝ :=
  1 / P.γ * Real.log (Real.sqrt (varU P τη α) /
    (1 / 2 * Real.sqrt (Vs P τη s (α ^ 2 * P.τu) P.ZH) + 1 / 2 * Real.sqrt (Vs P τη s (α ^ 2 * P.τu) P.ZL)))

noncomputable def Ls (P : Params) (τη s α : ℝ) : ℝ :=
  2 * P.γ * α * (P.ZH + (P.τu * α ^ 2 + τη) * s) * (P.ZL + (P.τu * α ^ 2 + τη) * s) /
    (τη * ((P.τu * α ^ 2 + τη) * (P.ZH + P.ZL) * s + 2 * P.ZH * P.ZL))

lemma Vs_eq (P : Params) (τη x p Z : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hx : 0 < x) (hp : 0 ≤ p)
    (hZ : 0 < Z) : Vs P τη (1 / x) p Z = condVar P τη (p + x * Z) := by
  rw [cv_eq]; unfold Vs
  have hk : 0 < P.τθ * τη / (P.τθ + τη) := by positivity
  have h1 : 0 < P.τθ * τη / (P.τθ + τη) + (p + x * Z) := by positivity
  have h2 : 0 < 1 / x * (P.τθ * τη / (P.τθ + τη) + p) + Z := by positivity
  congr 1
  rw [div_eq_div_iff h2.ne' h1.ne']
  field_simp
  ring

lemma Vs_zero (P : Params) (τη p Z : ℝ) : Vs P τη 0 p Z = 1 / (P.τθ + τη) := by
  simp [Vs]

lemma Vs_pos (P : Params) (τη s p Z : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hs : 0 ≤ s) (hp : 0 ≤ p)
    (hZ : 0 < Z) : 0 < Vs P τη s p Z := by
  unfold Vs
  have hk : 0 < P.τθ * τη / (P.τθ + τη) := by positivity
  positivity

lemma Gs_eq (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu) (hx : 0 < x)
    (hZH : 0 < P.ZH) (hZL : 0 < P.ZL) : Gs P τη (1 / x) α = gain P τη x α := by
  unfold Gs gain varH varL
  rw [Vs_eq P τη x _ _ hθ hτ hx (by positivity) hZH, Vs_eq P τη x _ _ hθ hτ hx (by positivity) hZL]

lemma Gs_zero (P : Params) (τη α : ℝ) : Gs P τη 0 α = gainAsIs P τη α := by
  unfold Gs gainAsIs
  rw [Vs_zero, Vs_zero]; ring_nf

lemma Ls_eq (P : Params) (τη x α : ℝ) (hτ : 0 < τη) (hu : 0 < P.τu) (hx : 0 < x)
    (hZH : 0 < P.ZH) (hZL : 0 < P.ZL) : Ls P τη (1 / x) α = lamOf P τη x α := by
  unfold Ls lamOf
  have hw : 0 < P.τu * α ^ 2 + τη := by positivity
  set w := P.τu * α ^ 2 + τη
  have h1 : 0 < w * (P.ZH + P.ZL) * (1 / x) + 2 * P.ZH * P.ZL := by positivity
  have h2 : 0 < w * (x * P.ZH + x * P.ZL) + 2 * (x * P.ZH) * (x * P.ZL) := by positivity
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp

lemma Ls_zero (P : Params) (τη α : ℝ) (hτ : 0 < τη) (hZH : 0 < P.ZH) (hZL : 0 < P.ZL) :
    Ls P τη 0 α = P.γ * α / τη := by
  unfold Ls
  simp only [mul_zero, add_zero, zero_mul]
  field_simp
  ring

lemma Ls_nonpos (P : Params) (τη s : ℝ) : Ls P τη s 0 = 0 := by simp [Ls]

lemma Ls_contOn (P : Params) (τη : ℝ) (hτ : 0 < τη) (hu : 0 < P.τu) (hZH : 0 < P.ZH) (hZL : 0 < P.ZL) :
    ContinuousOn (fun q : ℝ × ℝ => Ls P τη q.1 q.2) {q | 0 ≤ q.1} := by
  unfold Ls
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro q hq
  have : 0 < P.τu * q.2 ^ 2 + τη := by positivity
  have hq' : 0 ≤ q.1 := hq
  positivity

lemma Vs_contOn (P : Params) (τη Z : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu) (hZ : 0 < Z) :
    ContinuousOn (fun q : ℝ × ℝ => Vs P τη q.1 (q.2 ^ 2 * P.τu) Z) {q | 0 ≤ q.1} := by
  unfold Vs
  apply ContinuousOn.add continuousOn_const
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro q hq
  have hq' : 0 ≤ q.1 := hq
  have hk : 0 < P.τθ * τη / (P.τθ + τη) := by positivity
  positivity

lemma Gs_contOn (P : Params) (τη : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hZH : 0 < P.ZH) (hZL : 0 < P.ZL) :
    ContinuousOn (fun q : ℝ × ℝ => Gs P τη q.1 q.2) {q | 0 ≤ q.1} := by
  unfold Gs
  have cU := cv_cont P τη 0 hθ hτ hu le_rfl
  simp only [add_zero] at cU
  have cU' : ContinuousOn (fun q : ℝ × ℝ => varU P τη q.2) {q | 0 ≤ q.1} :=
    (cU.comp continuous_snd).continuousOn
  have cH := Vs_contOn P τη P.ZH hθ hτ hu hZH
  have cL := Vs_contOn P τη P.ZL hθ hτ hu hZL
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.log
  · apply ContinuousOn.div (Real.continuous_sqrt.comp_continuousOn cU')
    · exact ((Real.continuous_sqrt.comp_continuousOn cH).const_smul (1/2 : ℝ)).add
        ((Real.continuous_sqrt.comp_continuousOn cL).const_smul (1/2 : ℝ)) |>.congr
        (fun q _ => by simp [smul_eq_mul])
    · intro q hq
      have := Real.sqrt_pos.mpr (Vs_pos P τη q.1 (q.2 ^ 2 * P.τu) P.ZH hθ hτ hq (by positivity) hZH)
      have := Real.sqrt_nonneg (Vs P τη q.1 (q.2 ^ 2 * P.τu) P.ZL)
      positivity
  · intro q hq
    have := Real.sqrt_pos.mpr (Vs_pos P τη q.1 (q.2 ^ 2 * P.τu) P.ZH hθ hτ hq (by positivity) hZH)
    have := Real.sqrt_nonneg (Vs P τη q.1 (q.2 ^ 2 * P.τu) P.ZL)
    have := Real.sqrt_pos.mpr (cv_pos P τη (q.2 ^ 2 * P.τu) hθ hτ (by positivity))
    simp only [varU]
    positivity

lemma gainAsIs_le (P : Params) (τη α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hγ : 0 < P.γ) :
    gainAsIs P τη α ≤ 1 / P.γ * Real.log (Real.sqrt (condVar P τη 0) / Real.sqrt (1 / (P.τθ + τη))) := by
  unfold gainAsIs
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hp0 : 0 ≤ α ^ 2 * P.τu := by positivity
  have hA0 : 0 < 1 / (P.τθ + τη) := by positivity
  have hsA : 0 < Real.sqrt (1 / (P.τθ + τη)) := Real.sqrt_pos.mpr hA0
  have hU := cv_pos P τη _ hθ hτ hp0
  have hU0 := cv_anti_le P τη 0 _ hθ hτ le_rfl hp0
  apply Real.log_le_log
  · exact div_pos (Real.sqrt_pos.mpr hU) hsA
  · exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hU0) hsA.le

/-- ratio lower bound `V(P+z)/V(P) ≥ k/(k+z)` -/
lemma cv_ratio_ge (P : Params) (τη p z : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hp : 0 ≤ p) (hz : 0 ≤ z) :
    (P.τθ * τη / (P.τθ + τη)) / (P.τθ * τη / (P.τθ + τη) + z) ≤ condVar P τη (p + z) / condVar P τη p := by
  have hU := cv_pos P τη p hθ hτ hp
  rw [le_div_iff₀ hU, cv_eq, cv_eq]
  set a := 1 / (P.τθ + τη)
  set b := (τη / (P.τθ + τη)) ^ 2
  set k := P.τθ * τη / (P.τθ + τη) with hk
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hk0 : 0 < k := by positivity
  clear_value a b k
  have e1 : a + b / (k + (p + z)) = (a * (k + p + z) + b) / (k + p + z) := by
    field_simp; ring
  have e2 : a + b / (k + p) = (a * (k + p) + b) / (k + p) := by field_simp
  rw [e1, e2, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (a * (k + p + z) + b) * ((k + z) * (k + p)) - k * (a * (k + p) + b) * (k + p + z)
      = z * (a * k ^ 2 + 2 * a * k * p + a * k * z + a * p ^ 2 + a * p * z + b * p) := by ring
  have : 0 ≤ z * (a * k ^ 2 + 2 * a * k * p + a * k * z + a * p ^ 2 + a * p * z + b * p) := by positivity
  nlinarith

lemma gain_le_lin (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hγ : 0 < P.γ) (hx : 0 < x) (hZL : 0 < P.ZL) (hZ : P.ZL < P.ZH) :
    gain P τη x α ≤ x * P.ZH / (2 * P.γ * (P.τθ * τη / (P.τθ + τη))) := by
  have hZH : 0 < P.ZH := by linarith
  have hxH : 0 < x * P.ZH := mul_pos hx hZH
  have hxL : 0 < x * P.ZL := mul_pos hx hZL
  rw [gain_eq P τη x α hθ hτ hu hxH.le hxL.le]
  set k := P.τθ * τη / (P.τθ + τη) with hk
  have hk0 : 0 < k := by positivity
  set ρ := k / (k + x * P.ZH) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hp0 : 0 ≤ α ^ 2 * P.τu := by positivity
  have rH := cv_ratio_ge P τη (α ^ 2 * P.τu) (x * P.ZH) hθ hτ hp0 hxH.le
  have rL := cv_ratio_ge P τη (α ^ 2 * P.τu) (x * P.ZL) hθ hτ hp0 hxL.le
  have hLH : ρ ≤ k / (k + x * P.ZL) := by
    apply div_le_div_of_nonneg_left hk0.le (by positivity)
    have := mul_le_mul_of_nonneg_left hZ.le hx.le
    linarith
  simp only [varU, varH, varL]
  have sH : Real.sqrt ρ ≤ Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZH) / condVar P τη (α ^ 2 * P.τu)) :=
    Real.sqrt_le_sqrt rH
  have sL : Real.sqrt ρ ≤ Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZL) / condVar P τη (α ^ 2 * P.τu)) :=
    Real.sqrt_le_sqrt (le_trans hLH rL)
  have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ0
  have hlog : Real.log (Real.sqrt ρ) ≤ Real.log (1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZH) / condVar P τη (α ^ 2 * P.τu))
      + 1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZL) / condVar P τη (α ^ 2 * P.τu))) :=
    Real.log_le_log hsρ (by linarith)
  rw [Real.log_sqrt hρ0.le] at hlog
  have hl2 : -Real.log ρ ≤ x * P.ZH / k := by
    have : Real.log ρ⁻¹ ≤ ρ⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hρ0)
    rw [Real.log_inv] at this
    have e : ρ⁻¹ - 1 = x * P.ZH / k := by rw [hρ]; field_simp; ring
    linarith
  have hg : 0 < 1 / P.γ := by positivity
  have : -(1 / P.γ) * Real.log (1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZH) / condVar P τη (α ^ 2 * P.τu))
      + 1 / 2 * Real.sqrt (condVar P τη (α ^ 2 * P.τu + x * P.ZL) / condVar P τη (α ^ 2 * P.τu)))
      ≤ 1 / P.γ * (x * P.ZH / k / 2) := by nlinarith
  calc _ ≤ 1 / P.γ * (x * P.ZH / k / 2) := this
    _ = x * P.ZH / (2 * P.γ * k) := by field_simp

end GRUpair

open GRUpair

theorem solution (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ)
    (hC : IsCostFamily C) (c τη : ℝ) (hc : 0 < c) (hτη : 0 < τη) :
    ∃ (X : Clarity) (lam α : ℝ), IsEquilibrium P C c τη X lam α := by
  have hP' := hP
  obtain ⟨hθ, hu, hγ, hβ0, hβ1, hZL, hZ⟩ := hP
  obtain ⟨hCc, hCm, hC0, hCt⟩ := hC.1 c hc
  have hZH : 0 < P.ZH := by linarith
  have h1β : 0 < 1 - P.β := by linarith
  obtain ⟨⟨l0, a0⟩, hfe0, -⟩ :=
    SkillData.GoldRush.unique_pair_of_clarity P hP' C hC c τη 1 hc hτη one_pos
  have hfe0' := hfe0
  obtain ⟨-, hl0, hl01, ha0, h140, h190⟩ := hfe0
  simp only at hl0 hl01 ha0 h140 h190
  have Cnonneg : ∀ l, 0 ≤ l → l < 1 → 0 ≤ C c l := by
    intro l hl hl1
    rw [← hC0]; exact hCm.monotoneOn ⟨le_rfl, zero_lt_one⟩ ⟨hl, hl1⟩ hl
  have hc0 : 0 < C c l0 := by rw [← hC0]; exact hCm ⟨le_rfl, zero_lt_one⟩ ⟨hl0.le, hl01⟩ hl0
  set Mb := 1 / P.γ * Real.log (Real.sqrt (condVar P τη 0) / Real.sqrt (1 / (P.τθ + τη))) with hMb
  obtain ⟨lm, hlm1, hlm2⟩ := ((hCt.eventually (eventually_gt_atTop ((1 - P.β) * Mb))).and
    (Ioo_mem_nhdsLT hl01)).exists
  have hlm1' : (1 - P.β) * Mb < C c lm := hlm1
  set k := P.τθ * τη / (P.τθ + τη) with hk
  have hk0 : 0 < k := by positivity
  set x0 := P.γ * k * C c l0 / ((1 - P.β) * P.ZH) with hx0
  have hx0pos : 0 < x0 := by positivity
  -- bounds on feasible tuples
  have bound_l : ∀ X l a, Feasible P C c τη X l a → l < lm := by
    intro X l a hF
    by_contra hcon
    push_neg at hcon
    cases X with
    | finite x =>
      obtain ⟨hx, hl, hl1, ha, -, h19⟩ := hF
      have := gain_le P τη x a hθ hτη hu hγ (mul_pos hx hZH).le (mul_pos hx hZL).le
      have h2 : C c lm ≤ C c l := hCm.monotoneOn ⟨hlm2.1.le.trans' hl0.le, hlm2.2⟩ ⟨hl.le, hl1⟩ hcon
      have := mul_le_mul_of_nonneg_left this h1β.le
      linarith
    | asIs =>
      obtain ⟨hl, hl1, ha, -, h19⟩ := hF
      have := gainAsIs_le P τη a hθ hτη hu hγ
      have h2 : C c lm ≤ C c l := hCm.monotoneOn ⟨hlm2.1.le.trans' hl0.le, hlm2.2⟩ ⟨hl.le, hl1⟩ hcon
      have := mul_le_mul_of_nonneg_left this h1β.le
      linarith
  have bound_x : ∀ x l a, Feasible P C c τη (.finite x) l a → l0 ≤ l → x0 < x := by
    intro x l a hF hl0l
    obtain ⟨hx, hl, hl1, ha, -, h19⟩ := hF
    have hg := gain_le_lin P τη x a hθ hτη hu hγ hx hZL hZ
    have h2 : C c l0 ≤ C c l := hCm.monotoneOn ⟨hl0.le, hl01⟩ ⟨hl.le, hl1⟩ hl0l
    have h3 : C c l0 ≤ (1 - P.β) * (x * P.ZH / (2 * P.γ * k)) := by
      have := mul_le_mul_of_nonneg_left hg h1β.le
      linarith
    have h4 : x0 * 2 ≤ x := by
      rw [hx0]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have e : (1 - P.β) * (x * P.ZH / (2 * P.γ * k)) * (2 * P.γ * k) = (1 - P.β) * (x * P.ZH) := by
        field_simp
      have := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ 2 * P.γ * k)
      nlinarith
    linarith
  have bound_a : ∀ X l a, Feasible P C c τη X l a → a < τη / P.γ := by
    intro X l a hF
    cases X with
    | finite x =>
      obtain ⟨hx, hl, hl1, ha, h14, -⟩ := hF
      have hl' := (eq14_iff P τη x l a hτη hu (mul_pos hx hZH) (mul_pos hx hZL)).mp h14
      have := lamOf_gt P τη x a hτη hu hγ (mul_pos hx hZH) (mul_pos hx hZL) ha
      rw [← hl'] at this
      rw [lt_div_iff₀ hγ]
      rw [div_lt_iff₀ hτη] at this
      nlinarith
    | asIs =>
      obtain ⟨hl, hl1, ha, h, -⟩ := hF
      rw [lt_div_iff₀ hγ]
      nlinarith
  -- the compact set
  set s1 := 1 / x0 with hs1
  set B : Set (ℝ × ℝ) := Set.Icc 0 s1 ×ˢ Set.Icc 0 (τη / P.γ) with hB
  have hBsub : B ⊆ {q | 0 ≤ q.1} := fun q hq => hq.1.1
  have hBc : IsClosed B := isClosed_Icc.prod isClosed_Icc
  set Lf : ℝ × ℝ → ℝ := fun q => Ls P τη q.1 q.2 with hLf
  have LsB : ContinuousOn Lf B := (Ls_contOn P τη hτη hu hZH hZL).mono hBsub
  have GsB : ContinuousOn (fun q : ℝ × ℝ => Gs P τη q.1 q.2) B :=
    (Gs_contOn P τη hθ hτη hu hZH hZL).mono hBsub
  set D1 := B ∩ Lf ⁻¹' Set.Icc l0 lm with hD1
  have hD1c : IsClosed D1 := LsB.preimage_isClosed_of_isClosed hBc isClosed_Icc
  set Ff : ℝ × ℝ → ℝ := fun q => (1 - P.β) * Gs P τη q.1 q.2 - C c (Ls P τη q.1 q.2) with hFf
  have FD1 : ContinuousOn Ff D1 := by
    apply ContinuousOn.sub
    · exact continuousOn_const.mul (GsB.mono Set.inter_subset_left)
    · exact hCc.comp (LsB.mono Set.inter_subset_left)
        (fun q hq => ⟨le_trans hl0.le hq.2.1, lt_of_le_of_lt hq.2.2 hlm2.2⟩)
  set K := D1 ∩ Ff ⁻¹' {0} with hK
  have hKc : IsClosed K := FD1.preimage_isClosed_of_isClosed hD1c isClosed_singleton
  have hKcomp : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKc (fun q hq => hq.1.1)
  -- feasible tuples with l ≥ l0 give points of K
  have memK_fin : ∀ x l a, Feasible P C c τη (.finite x) l a → l0 ≤ l → ((1 / x, a) : ℝ × ℝ) ∈ K ∧
      Lf (1 / x, a) = l := by
    intro x l a hF hl0l
    have hxx := bound_x x l a hF hl0l
    have hal := bound_a _ l a hF
    have hll := bound_l _ l a hF
    obtain ⟨hx, hl, hl1, ha, h14, h19⟩ := hF
    have hLeq : Lf (1 / x, a) = l := by
      simp only [hLf]
      rw [Ls_eq P τη x a hτη hu hx hZH hZL]
      exact ((eq14_iff P τη x l a hτη hu (mul_pos hx hZH) (mul_pos hx hZL)).mp h14).symm
    refine ⟨⟨⟨⟨⟨by positivity, ?_⟩, ⟨ha.le, hal.le⟩⟩, ?_⟩, ?_⟩, hLeq⟩
    · simp only [hs1]
      exact one_div_le_one_div_of_le hx0pos hxx.le
    · show Lf (1 / x, a) ∈ Set.Icc l0 lm
      rw [hLeq]; exact ⟨hl0l, hll.le⟩
    · show Ff (1 / x, a) = 0
      simp only [hFf]
      have := hLeq; simp only [hLf] at this
      rw [this, Gs_eq P τη x a hθ hτη hu hx hZH hZL, h19]; ring
  have memK_as : ∀ l a, Feasible P C c τη .asIs l a → l0 ≤ l → ((0, a) : ℝ × ℝ) ∈ K ∧
      Lf (0, a) = l := by
    intro l a hF hl0l
    have hal := bound_a _ l a hF
    have hll := bound_l _ l a hF
    obtain ⟨hl, hl1, ha, h, h19⟩ := hF
    have hLeq : Lf (0, a) = l := by
      simp only [hLf]
      rw [Ls_zero P τη a hτη hZH hZL, h]; field_simp
    refine ⟨⟨⟨⟨⟨le_rfl, by positivity⟩, ⟨ha.le, hal.le⟩⟩, ?_⟩, ?_⟩, hLeq⟩
    · show Lf (0, a) ∈ Set.Icc l0 lm
      rw [hLeq]; exact ⟨hl0l, hll.le⟩
    · show Ff (0, a) = 0
      simp only [hFf]
      have := hLeq; simp only [hLf] at this
      rw [this, Gs_zero, h19]; ring
  have hne : K.Nonempty := ⟨_, (memK_fin 1 l0 a0 hfe0' le_rfl).1⟩
  obtain ⟨q, hqK, hmax⟩ := hKcomp.exists_isMaxOn hne (LsB.mono (fun q hq => hq.1.1))
  obtain ⟨s, α⟩ := q
  have hs0 : 0 ≤ s := hqK.1.1.1.1
  have hα0 : 0 ≤ α := hqK.1.1.2.1
  have hLq : Lf (s, α) ∈ Set.Icc l0 lm := hqK.1.2
  have hFq : Ff (s, α) = 0 := hqK.2
  simp only [hFf] at hFq
  set lh := Ls P τη s α with hlh
  have hlhpos : 0 < lh := lt_of_lt_of_le hl0 hLq.1
  have hlh1 : lh < 1 := lt_of_le_of_lt hLq.2 hlm2.2
  have hαpos : 0 < α := by
    rcases eq_or_lt_of_le hα0 with h | h
    · exfalso
      have : lh = 0 := by rw [hlh, ← h, Ls_nonpos]
      linarith
    · exact h
  -- profit monotonicity
  have profit_le : ∀ X' l' a', Feasible P C c τη X' l' a' → ∀ X, Feasible P C c τη X lh α →
      profit P τη X' l' a' ≤ profit P τη X lh α := by
    intro X' l' a' hF' X hF
    have hl'le : l' ≤ lh := by
      by_cases h : l0 ≤ l'
      · cases X' with
        | finite x' =>
          obtain ⟨hm, he⟩ := memK_fin x' l' a' hF' h
          rw [← he]; exact hmax hm
        | asIs =>
          obtain ⟨hm, he⟩ := memK_as l' a' hF' h
          rw [← he]; exact hmax hm
      · push_neg at h; linarith [hLq.1]
    have hl'0 : 0 < l' := by cases X' with
      | finite x' => exact hF'.2.1
      | asIs => exact hF'.1
    rw [SkillData.GoldRush.eq_C5 P hP' C c τη X' l' a' hF', SkillData.GoldRush.eq_C5 P hP' C c τη X lh α hF]
    have hC1 : C c l' ≤ C c lh := hCm.monotoneOn ⟨hl'0.le, lt_of_le_of_lt hl'le hlh1⟩ ⟨hlhpos.le, hlh1⟩ hl'le
    have hC2 : 0 ≤ C c l' := Cnonneg l' hl'0.le (lt_of_le_of_lt hl'le hlh1)
    apply div_le_div_of_nonneg_right _ h1β.le
    have : l' * C c l' ≤ lh * C c lh := by nlinarith
    nlinarith
  rcases eq_or_lt_of_le hs0 with hs | hs
  · -- as is
    subst hs
    have hF : Feasible P C c τη .asIs lh α := by
      refine ⟨hlhpos, hlh1, hαpos, ?_, ?_⟩
      · rw [hlh, Ls_zero P τη α hτη hZH hZL]; field_simp
      · rw [← Gs_zero]; linarith
    exact ⟨.asIs, lh, α, hF, fun X' l' a' hF' => profit_le X' l' a' hF' _ hF⟩
  · -- finite clarity x = 1/s
    have hx : 0 < 1 / s := by positivity
    have hs' : 1 / (1 / s) = s := by field_simp
    have hF : Feasible P C c τη (.finite (1 / s)) lh α := by
      refine ⟨hx, hlhpos, hlh1, hαpos, ?_, ?_⟩
      · apply (eq14_iff P τη (1 / s) lh α hτη hu (mul_pos hx hZH) (mul_pos hx hZL)).mpr
        rw [← Ls_eq P τη (1 / s) α hτη hu hx hZH hZL, hs']
      · rw [← Gs_eq P τη (1 / s) α hθ hτη hu hx hZH hZL, hs']; linarith
    exact ⟨.finite (1 / s), lh, α, hF, fun X' l' a' hF' => profit_le X' l' a' hF' _ hF⟩
