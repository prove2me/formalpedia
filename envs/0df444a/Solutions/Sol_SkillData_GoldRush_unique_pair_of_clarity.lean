-- Prove2me | solution 1 for SkillData.GoldRush.unique_pair_of_clarity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T01:28:29.591278+00:00
-- url     : https://prove2.me/submissions/219be4bd-9a93-4644-b689-2722ce49e5e7

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

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

end GRUpair

open GRUpair

theorem solution (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ)
    (hC : IsCostFamily C) (c τη x : ℝ) (hc : 0 < c) (hτη : 0 < τη) (hx : 0 < x) :
    ∃! p : ℝ × ℝ, Feasible P C c τη (.finite x) p.1 p.2 := by
  obtain ⟨hθ, hu, hγ, hβ0, hβ1, hZL, hZ⟩ := hP
  obtain ⟨hCc, hCm, hC0, hCt⟩ := hC.1 c hc
  have hxH : 0 < x * P.ZH := mul_pos hx (by linarith)
  have hxL : 0 < x * P.ZL := mul_pos hx hZL
  have h1β : 0 < 1 - P.β := by linarith
  set L := fun α => lamOf P τη x α with hL
  have Lcont : Continuous L := lamOf_cont P τη x hτη hu hxH hxL
  have L0 : L 0 = 0 := by simp [hL, lamOf]
  -- α₁ with L α₁ = 1
  have hTg : 1 ≤ L (τη / P.γ) := by
    have := lamOf_gt P τη x (τη / P.γ) hτη hu hγ hxH hxL (by positivity)
    have e : P.γ * (τη / P.γ) / τη = 1 := by field_simp
    rw [e] at this; exact this.le
  obtain ⟨α₁, hα₁I, hα₁⟩ : ∃ α₁ ∈ Set.Icc (0:ℝ) (τη / P.γ), L α₁ = 1 :=
    intermediate_value_Icc (by positivity) Lcont.continuousOn ⟨by rw [L0]; norm_num, hTg⟩
  have hα₁pos : 0 < α₁ := by
    rcases eq_or_lt_of_le hα₁I.1 with h | h
    · rw [← h, L0] at hα₁; norm_num at hα₁
    · exact h
  have Lrange : ∀ α ∈ Set.Ico (0:ℝ) α₁, L α ∈ Set.Ico (0:ℝ) 1 := by
    intro α hα
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hα.1 with h | h
      · rw [← h, L0]
      · exact (lamOf_pos P τη x α hτη hu hγ hxH hxL h).le
    · rw [← hα₁]; exact lamOf_strictMono P τη x α α₁ hτη hu hγ hxH hxL hα.1 hα.2
  have CLcont : ContinuousOn (fun α => C c (L α)) (Set.Ico 0 α₁) :=
    hCc.comp Lcont.continuousOn (fun α hα => Lrange α hα)
  have Gcont := gain_cont P τη x hθ hτη hu hxH.le hxL.le
  set F := fun α => (1 - P.β) * gain P τη x α - C c (L α) with hF
  -- a point with F > 0
  set g0 := (1 - P.β) * gain P τη x α₁ with hg0
  have hg0 : 0 < g0 := mul_pos h1β (gain_pos P τη x α₁ hθ hτη hu hγ hxH hxL)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.mp
    (CLcont (0:ℝ) ⟨le_rfl, hα₁pos⟩) g0 hg0
  set αs := min (δ / 2) (α₁ / 2) with hαs
  have hαspos : 0 < αs := by positivity
  have hαslt : αs < α₁ := by
    have : αs ≤ α₁ / 2 := min_le_right _ _
    linarith
  have hFs : 0 < F αs := by
    have hd : dist αs 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hαspos]
      have : αs ≤ δ / 2 := min_le_left _ _
      linarith
    have := hδ' ⟨hαspos.le, hαslt⟩ hd
    rw [L0, hC0, Real.dist_eq, sub_zero] at this
    have h2 := (abs_lt.mp this).2
    have h3 := gain_strictAnti P τη x αs α₁ hθ hτη hu hγ hxH hxL hαspos.le hαslt
    have h4 : (1 - P.β) * gain P τη x α₁ < (1 - P.β) * gain P τη x αs := mul_lt_mul_of_pos_left h3 h1β
    simp only [hF]; linarith
  -- a point with F < 0
  set Mb := 1 / P.γ * Real.log (Real.sqrt (condVar P τη 0) / Real.sqrt (1 / (P.τθ + τη))) with hMb
  have hLt : Filter.Tendsto L (𝓝[<] α₁) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have := Lcont.tendsto α₁
      rw [hα₁] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT hα₁pos] with y hy
      rw [Set.mem_Iio, ← hα₁]
      exact lamOf_strictMono P τη x y α₁ hτη hu hγ hxH hxL hy.1.le hy.2
  have hCL := hCt.comp hLt
  obtain ⟨y, hy1, hy2⟩ := ((hCL.eventually (Filter.eventually_gt_atTop ((1 - P.β) * Mb))).and
    (Ioo_mem_nhdsLT hαslt)).exists
  have hFy : F y < 0 := by
    have := gain_le P τη x y hθ hτη hu hγ hxH.le hxL.le
    have h4 : (1 - P.β) * gain P τη x y ≤ (1 - P.β) * Mb := mul_le_mul_of_nonneg_left this h1β.le
    simp only [hF]
    simp only [Function.comp] at hy1
    linarith
  have Fcont : ContinuousOn F (Set.Icc αs y) := by
    apply ContinuousOn.sub
    · exact (continuous_const.mul Gcont).continuousOn
    · exact CLcont.mono (fun z hz => ⟨le_trans hαspos.le hz.1, lt_of_le_of_lt hz.2 hy2.2⟩)
  obtain ⟨αe, hαeI, hαe⟩ : ∃ αe ∈ Set.Icc αs y, F αe = 0 :=
    intermediate_value_Icc' hy2.1.le Fcont ⟨hFy.le, hFs.le⟩
  have hαepos : 0 < αe := lt_of_lt_of_le hαspos hαeI.1
  have hαelt : αe < α₁ := lt_of_le_of_lt hαeI.2 hy2.2
  have hLe := Lrange αe ⟨hαepos.le, hαelt⟩
  refine ⟨(L αe, αe), ?_, ?_⟩
  · refine ⟨hx, lamOf_pos P τη x αe hτη hu hγ hxH hxL hαepos, hLe.2, hαepos,
      (eq14_iff P τη x _ αe hτη hu hxH hxL).mpr rfl, ?_⟩
    have : F αe = 0 := hαe
    simp only [hF] at this
    linarith
  · rintro ⟨l, a⟩ ⟨-, hl0, hl1, ha0, h14, h19⟩
    simp only at hl0 hl1 ha0 h14 h19 ⊢
    have hl : l = L a := (eq14_iff P τη x l a hτη hu hxH hxL).mp h14
    have hFe : (1 - P.β) * gain P τη x αe = C c (L αe) := by
      have : F αe = 0 := hαe
      simp only [hF] at this; linarith
    have haeq : a = αe := by
      rcases lt_trichotomy a αe with h | h | h
      · exfalso
        have g1 := mul_lt_mul_of_pos_left (gain_strictAnti P τη x a αe hθ hτη hu hγ hxH hxL ha0.le h) h1β
        have l1 : L a < L αe := lamOf_strictMono P τη x a αe hτη hu hγ hxH hxL ha0.le h
        have c1 : C c (L a) < C c (L αe) :=
          hCm ⟨by rw [← hl]; exact hl0.le, by rw [← hl]; exact hl1⟩ hLe l1
        rw [← hl] at c1
        linarith
      · exact h
      · exfalso
        have g1 := mul_lt_mul_of_pos_left (gain_strictAnti P τη x αe a hθ hτη hu hγ hxH hxL hαepos.le h) h1β
        have l1 : L αe < L a := lamOf_strictMono P τη x αe a hτη hu hγ hxH hxL hαepos.le h
        have c1 : C c (L αe) < C c (L a) :=
          hCm hLe ⟨by rw [← hl]; exact hl0.le, by rw [← hl]; exact hl1⟩ l1
        rw [← hl] at c1
        linarith
    rw [haeq] at hl
    rw [hl, haeq]
