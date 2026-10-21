-- Prove2me | solution 1 for SkillData.GoldRush.proposition_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T02:47:32.678495+00:00
-- url     : https://prove2.me/submissions/31909ae9-227a-48a0-b1a5-2a33ee7af6e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model
import Theorems.Thm_SkillData_GoldRush_unique_pair_of_clarity
import Theorems.Thm_SkillData_GoldRush_eq_C5
import Theorems.Thm_SkillData_GoldRush_proposition_5_market_quality

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



open SkillData.GoldRush Filter Topology GRUpair

namespace GRAsym

noncomputable def fr (y : ℝ) : ℝ := 1 / Real.sqrt (1 + y)

lemma fr_diff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    fr a - fr b = (b - a) / ((Real.sqrt (1 + a) + Real.sqrt (1 + b)) * Real.sqrt (1 + a) * Real.sqrt (1 + b)) := by
  unfold fr
  have h1 : 1 ≤ Real.sqrt (1 + a) := by rw [Real.le_sqrt] <;> linarith
  have h2 : 1 ≤ Real.sqrt (1 + b) := by rw [Real.le_sqrt] <;> linarith
  have e1 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + a)
  have e2 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + b)
  rw [div_sub_div _ _ (by positivity) (by positivity), div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (Real.sqrt (1 + a) * Real.sqrt (1 + b)) * (e2 - e1)

lemma fr_lip (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : |fr a - fr b| ≤ |a - b| / 2 := by
  rw [fr_diff a b ha hb]
  have h1 : 1 ≤ Real.sqrt (1 + a) := by rw [Real.le_sqrt] <;> linarith
  have h2 : 1 ≤ Real.sqrt (1 + b) := by rw [Real.le_sqrt] <;> linarith
  have hD : 2 ≤ (Real.sqrt (1 + a) + Real.sqrt (1 + b)) * Real.sqrt (1 + a) * Real.sqrt (1 + b) := by
    nlinarith [mul_le_mul h1 h2 zero_le_one (by linarith)]
  have hDp : 0 < (Real.sqrt (1 + a) + Real.sqrt (1 + b)) * Real.sqrt (1 + a) * Real.sqrt (1 + b) := by
    linarith
  rw [abs_div, abs_of_pos hDp, abs_sub_comm b a]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hD

lemma fr_gap (a b Y : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbY : b ≤ Y) :
    (b - a) / (2 * (1 + Y) * Real.sqrt (1 + Y)) ≤ fr a - fr b := by
  have hb : 0 ≤ b := le_trans ha hab
  rw [fr_diff a b ha hb]
  have h1 : 1 ≤ Real.sqrt (1 + a) := by rw [Real.le_sqrt] <;> linarith
  have h2 : 1 ≤ Real.sqrt (1 + b) := by rw [Real.le_sqrt] <;> linarith
  have sa : Real.sqrt (1 + a) ≤ Real.sqrt (1 + Y) := Real.sqrt_le_sqrt (by linarith)
  have sb : Real.sqrt (1 + b) ≤ Real.sqrt (1 + Y) := Real.sqrt_le_sqrt (by linarith)
  have eY := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + Y)
  apply div_le_div_of_nonneg_left (by linarith) (by positivity)
  have hsY : 0 ≤ Real.sqrt (1 + Y) := Real.sqrt_nonneg _
  calc (Real.sqrt (1 + a) + Real.sqrt (1 + b)) * Real.sqrt (1 + a) * Real.sqrt (1 + b)
      ≤ (Real.sqrt (1 + Y) + Real.sqrt (1 + Y)) * Real.sqrt (1 + Y) * Real.sqrt (1 + Y) := by
        apply mul_le_mul (mul_le_mul (by linarith) sa (by linarith) (by positivity)) sb (by linarith) (by positivity)
    _ = 2 * (1 + Y) * Real.sqrt (1 + Y) := by nlinarith [eY]

lemma fr_anti (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : fr b ≤ fr a := by
  have := fr_gap a b b ha hab le_rfl
  have : 0 ≤ (b - a) / (2 * (1 + b) * Real.sqrt (1 + b)) := by
    have : 0 ≤ b := le_trans ha hab
    apply div_nonneg (by linarith); positivity
  linarith

lemma fr_strictAnti (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : fr b < fr a := by
  have := fr_gap a b b ha hab.le le_rfl
  have : 0 < (b - a) / (2 * (1 + b) * Real.sqrt (1 + b)) := by
    have : 0 ≤ b := le_trans ha hab.le
    have : 0 < Real.sqrt (1 + b) := Real.sqrt_pos.mpr (by linarith)
    apply div_pos (by linarith); positivity
  linarith

lemma fr_pos (a : ℝ) (ha : 0 ≤ a) : 0 < fr a := by
  unfold fr; have : 0 < Real.sqrt (1 + a) := Real.sqrt_pos.mpr (by linarith); positivity

lemma fr_le_one (a : ℝ) (ha : 0 ≤ a) : fr a ≤ 1 := by
  have := fr_anti 0 a le_rfl ha
  simpa [fr] using this

lemma fr_cont : ContinuousOn fr (Set.Ici 0) := by
  unfold fr
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro y hy; have : (0:ℝ) ≤ y := hy
  exact (Real.sqrt_pos.mpr (by linarith)).ne'

/-- `sqrt (V(p+z)/V(p)) = fr (V(p)/V(p+z) - 1)` -/
lemma sqrt_ratio_eq (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Real.sqrt (B / A) = fr (A / B - 1) := by
  unfold fr
  rw [show 1 + (A / B - 1) = A / B by ring, Real.sqrt_div' _ hB.le, Real.sqrt_div' _ hA.le]
  have : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  field_simp

/-- closed form of the conditional variance -/
lemma cv_alt (P : Params) (τη p : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hp : 0 ≤ p) :
    condVar P τη p = (τη + p) / ((P.τθ + τη) * (P.τθ * τη / (P.τθ + τη) + p)) := by
  rw [cv_eq]
  have hk : 0 < P.τθ * τη / (P.τθ + τη) + p := by positivity
  rw [eq_div_iff (by positivity)]
  field_simp
  ring


/-- the price-signal factor `r1` -/
noncomputable def r1 (P : Params) (τη p : ℝ) : ℝ :=
  τη * (P.τθ + p) / ((P.τθ + τη) * (P.τθ * τη / (P.τθ + τη) + p))

noncomputable def r2H (P : Params) (τη x p : ℝ) : ℝ :=
  (P.ZH + P.ZL) * (x * P.ZL + (p + τη)) / ((p + τη) * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL)

noncomputable def r2L (P : Params) (τη x p : ℝ) : ℝ :=
  (P.ZH + P.ZL) * (x * P.ZH + (p + τη)) / ((p + τη) * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL)

lemma y_eq_gen (P : Params) (τη x α Z W : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hx : 0 < x) (hZ : 0 < Z) (hW : 0 < W) (hα : 0 < α) (hγ : 0 < P.γ)
    (hZH : P.ZH = Z ∨ P.ZH = W) (hZL : (P.ZH = Z ∧ P.ZL = W) ∨ (P.ZH = W ∧ P.ZL = Z)) :
    condVar P τη (α ^ 2 * P.τu) / condVar P τη (α ^ 2 * P.τu + x * Z) - 1 =
      (2 * P.γ * Z / (Z + W)) * (α / (P.τθ + α ^ 2 * P.τu)) / lamOf P τη x α * r1 P τη (α ^ 2 * P.τu)
        * ((Z + W) * (x * W + (α ^ 2 * P.τu + τη)) / ((α ^ 2 * P.τu + τη) * (Z + W) + 2 * x * Z * W)) := by
  have hp : 0 ≤ α ^ 2 * P.τu := by positivity
  rw [cv_alt P τη _ hθ hτ hp, cv_alt P τη _ hθ hτ (by positivity)]
  have hlam : lamOf P τη x α = 2 * P.γ * α * (x * Z + (α ^ 2 * P.τu + τη)) * (x * W + (α ^ 2 * P.τu + τη)) /
      (τη * ((α ^ 2 * P.τu + τη) * (x * Z + x * W) + 2 * (x * Z) * (x * W))) := by
    unfold lamOf
    rcases hZL with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, mul_comm P.τu (α ^ 2)] <;> ring
  rw [hlam]
  unfold r1
  set p := α ^ 2 * P.τu with hpdef
  set k := P.τθ * τη / (P.τθ + τη) with hk
  have hk0 : 0 < k := by positivity
  have e : k * (P.τθ + τη) = P.τθ * τη := by rw [hk]; field_simp
  clear_value p k
  field_simp
  linear_combination (-(x * Z * (p + x * Z + τη))) * e

lemma r1_bounds (P : Params) (τη p : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hp : 0 ≤ p) :
    |r1 P τη p - 1| ≤ P.τθ / (P.τθ + τη) := by
  unfold r1
  have hk : 0 < P.τθ * τη / (P.τθ + τη) + p := by positivity
  have e : (P.τθ + τη) * (P.τθ * τη / (P.τθ + τη) + p) = P.τθ * τη + (P.τθ + τη) * p := by
    field_simp
  rw [e]
  have hD : 0 < P.τθ * τη + (P.τθ + τη) * p := by positivity
  have h1 : τη * (P.τθ + p) / (P.τθ * τη + (P.τθ + τη) * p) ≤ 1 := by
    rw [div_le_one hD]; nlinarith
  have h2 : τη / (P.τθ + τη) ≤ τη * (P.τθ + p) / (P.τθ * τη + (P.τθ + τη) * p) := by
    rw [div_le_div_iff₀ (by positivity) hD]; nlinarith [mul_nonneg hθ.le hp, mul_pos hθ hτ]
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have : 1 - τη / (P.τθ + τη) = P.τθ / (P.τθ + τη) := by field_simp; ring
  linarith

lemma r2_bounds (x u Z W τη : ℝ) (hx : 0 < x) (hZ : 0 < Z) (hW : 0 < W) (hτ : 0 < τη) (hu : τη ≤ u) :
    |(Z + W) * (x * W + u) / (u * (Z + W) + 2 * x * Z * W) - 1| ≤ x * W * |Z - W| / (τη * (Z + W)) := by
  have hu0 : 0 < u := lt_of_lt_of_le hτ hu
  have hD : 0 < u * (Z + W) + 2 * x * Z * W := by positivity
  have e : (Z + W) * (x * W + u) / (u * (Z + W) + 2 * x * Z * W) - 1
      = x * W * (W - Z) / (u * (Z + W) + 2 * x * Z * W) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos hD, abs_mul, abs_of_pos (by positivity : 0 < x * W), abs_sub_comm W Z]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : 0 ≤ 2 * x * Z * W := by positivity
  have := mul_le_mul_of_nonneg_right hu (by positivity : (0:ℝ) ≤ Z + W)
  linarith

lemma prod_bound (a b : ℝ) : |a * b - 1| ≤ |a - 1| * (1 + |b - 1|) + |b - 1| := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [e]
  have hb : |b| ≤ 1 + |b - 1| := by
    have := abs_add_le (b - 1) 1
    simp only [sub_add_cancel, abs_one] at this; linarith
  calc |(a - 1) * b + (b - 1)| ≤ |(a - 1) * b| + |b - 1| := abs_add_le _ _
    _ = |a - 1| * |b| + |b - 1| := by rw [abs_mul]
    _ ≤ |a - 1| * (1 + |b - 1|) + |b - 1| := by
        have := mul_le_mul_of_nonneg_left hb (abs_nonneg (a - 1)); linarith

/-- `m(x, α)`: the average of the two standard-deviation ratios entering `G` -/
noncomputable def mfun (P : Params) (τη x α : ℝ) : ℝ :=
  1 / 2 * Real.sqrt (varH P τη x α / varU P τη α) + 1 / 2 * Real.sqrt (varL P τη x α / varU P τη α)

noncomputable def qfun (P : Params) (Z lam h : ℝ) : ℝ := 2 * P.γ * Z / (P.ZH + P.ZL) * h / lam

noncomputable def hfun (P : Params) (α : ℝ) : ℝ := α / (P.τθ + α ^ 2 * P.τu)

noncomputable def rhoH (P : Params) (τη x α : ℝ) : ℝ :=
  r1 P τη (α ^ 2 * P.τu) * ((P.ZH + P.ZL) * (x * P.ZL + (α ^ 2 * P.τu + τη)) /
    ((α ^ 2 * P.τu + τη) * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL))

noncomputable def rhoL (P : Params) (τη x α : ℝ) : ℝ :=
  r1 P τη (α ^ 2 * P.τu) * ((P.ZL + P.ZH) * (x * P.ZH + (α ^ 2 * P.τu + τη)) /
    ((α ^ 2 * P.τu + τη) * (P.ZL + P.ZH) + 2 * x * P.ZL * P.ZH))

lemma mfun_eq (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hx : 0 < x) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH) (hα : 0 < α) (hγ : 0 < P.γ) :
    mfun P τη x α = 1 / 2 * fr (qfun P P.ZH (lamOf P τη x α) (hfun P α) * rhoH P τη x α)
      + 1 / 2 * fr (qfun P P.ZL (lamOf P τη x α) (hfun P α) * rhoL P τη x α) := by
  unfold mfun
  have hp : 0 ≤ α ^ 2 * P.τu := by positivity
  have hU := cv_pos P τη (α ^ 2 * P.τu) hθ hτ hp
  have hH := cv_pos P τη (α ^ 2 * P.τu + x * P.ZH) hθ hτ (by positivity)
  have hL := cv_pos P τη (α ^ 2 * P.τu + x * P.ZL) hθ hτ (by positivity)
  simp only [varU, varH, varL]
  rw [sqrt_ratio_eq _ _ hU hH, sqrt_ratio_eq _ _ hU hL]
  rw [y_eq_gen P τη x α P.ZH P.ZL hθ hτ hu hx hZH hZL hα hγ (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩)]
  rw [y_eq_gen P τη x α P.ZL P.ZH hθ hτ hu hx hZL hZH hα hγ (Or.inr rfl) (Or.inr ⟨rfl, rfl⟩)]
  unfold qfun hfun rhoH rhoL
  have e : P.ZL + P.ZH = P.ZH + P.ZL := add_comm _ _
  rw [e]
  ring_nf

lemma gain_mfun (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hxH : 0 ≤ x * P.ZH) (hxL : 0 ≤ x * P.ZL) :
    gain P τη x α = -(1 / P.γ) * Real.log (mfun P τη x α) := by
  rw [gain_eq P τη x α hθ hτ hu hxH hxL]; rfl

lemma mfun_pos (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hxH : 0 ≤ x * P.ZH) (hxL : 0 ≤ x * P.ZL) : 0 < mfun P τη x α := by
  unfold mfun varH varL varU
  have hp : 0 ≤ α ^ 2 * P.τu := by positivity
  have hU := cv_pos P τη (α ^ 2 * P.τu) hθ hτ hp
  have hH := cv_pos P τη (α ^ 2 * P.τu + x * P.ZH) hθ hτ (by positivity)
  have := Real.sqrt_pos.mpr (div_pos hH hU)
  have := Real.sqrt_nonneg (condVar P τη (α ^ 2 * P.τu + x * P.ZL) / condVar P τη (α ^ 2 * P.τu))
  positivity

/-- `E(λ) = exp(-γ C(c,λ)/(1-β))` -/
noncomputable def Efun (P : Params) (C : ℝ → ℝ → ℝ) (c lam : ℝ) : ℝ :=
  Real.exp (-(P.γ * C c lam / (1 - P.β)))

lemma feas_mfun (P : Params) (C : ℝ → ℝ → ℝ) (c τη x lam α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη)
    (hu : 0 < P.τu) (hγ : 0 < P.γ) (hβ1 : P.β < 1) (hxH : 0 ≤ x * P.ZH) (hxL : 0 ≤ x * P.ZL)
    (h19 : (1 - P.β) * gain P τη x α = C c lam) : mfun P τη x α = Efun P C c lam := by
  rw [gain_mfun P τη x α hθ hτ hu hxH hxL] at h19
  have hm := mfun_pos P τη x α hθ hτ hu hxH hxL
  unfold Efun
  have h1β : (1 - P.β) ≠ 0 := by linarith
  have : -(P.γ * C c lam / (1 - P.β)) = Real.log (mfun P τη x α) := by
    rw [← h19]; field_simp
  rw [this, Real.exp_log hm]

lemma feas_asIs (P : Params) (C : ℝ → ℝ → ℝ) (c τη lam α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη)
    (hu : 0 < P.τu) (hγ : 0 < P.γ) (hβ1 : P.β < 1)
    (h19 : (1 - P.β) * gainAsIs P τη α = C c lam) :
    Real.sqrt (1 / (P.τθ + τη)) / Real.sqrt (varU P τη α) = Efun P C c lam := by
  unfold gainAsIs at h19
  have hU := cv_pos P τη (α ^ 2 * P.τu) hθ hτ (by positivity)
  have hA : 0 < Real.sqrt (1 / (P.τθ + τη)) := Real.sqrt_pos.mpr (by positivity)
  have hsU : 0 < Real.sqrt (varU P τη α) := Real.sqrt_pos.mpr hU
  unfold Efun
  have h1β : (1 - P.β) ≠ 0 := by linarith
  have : -(P.γ * C c lam / (1 - P.β)) = Real.log (Real.sqrt (1 / (P.τθ + τη)) / Real.sqrt (varU P τη α)) := by
    rw [← h19, Real.log_div hA.ne' hsU.ne', Real.log_div hsU.ne' hA.ne']; field_simp; ring
  rw [this, Real.exp_log (div_pos hA hsU)]

noncomputable def Rfun (P : Params) (lam h : ℝ) : ℝ :=
  1 / 2 * fr (qfun P P.ZH lam h) + 1 / 2 * fr (qfun P P.ZL lam h)

noncomputable def hmax (P : Params) : ℝ := 1 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu)

lemma qfun_nonneg (P : Params) (Z lam h : ℝ) (hγ : 0 < P.γ) (hZ : 0 < Z) (hS : 0 < P.ZH + P.ZL)
    (hl : 0 < lam) (hh : 0 ≤ h) : 0 ≤ qfun P Z lam h := by
  unfold qfun; positivity

lemma hfun_nonneg (P : Params) (α : ℝ) (hθ : 0 < P.τθ) (hu : 0 < P.τu) (hα : 0 ≤ α) :
    0 ≤ hfun P α := by unfold hfun; positivity

lemma hmax_sub (P : Params) (α : ℝ) (hθ : 0 < P.τθ) (hu : 0 < P.τu) :
    hmax P - hfun P α = P.τu * (α - Real.sqrt (P.τθ / P.τu)) ^ 2 /
      (2 * Real.sqrt P.τθ * Real.sqrt P.τu * (P.τθ + α ^ 2 * P.τu)) := by
  unfold hmax hfun
  have st := Real.sq_sqrt hθ.le
  have su := Real.sq_sqrt hu.le
  have hst : 0 < Real.sqrt P.τθ := Real.sqrt_pos.mpr hθ
  have hsu : 0 < Real.sqrt P.τu := Real.sqrt_pos.mpr hu
  rw [Real.sqrt_div' _ hu.le]
  set a := Real.sqrt P.τθ
  set b := Real.sqrt P.τu
  clear_value a b
  rw [← st, ← su]
  have hD : 0 < a ^ 2 + α ^ 2 * b ^ 2 := by positivity
  field_simp
  ring

lemma hfun_le (P : Params) (α : ℝ) (hθ : 0 < P.τθ) (hu : 0 < P.τu) : hfun P α ≤ hmax P := by
  have := hmax_sub P α hθ hu
  have : 0 ≤ P.τu * (α - Real.sqrt (P.τθ / P.τu)) ^ 2 /
      (2 * Real.sqrt P.τθ * Real.sqrt P.τu * (P.τθ + α ^ 2 * P.τu)) := by
    have := Real.sqrt_pos.mpr hθ; have := Real.sqrt_pos.mpr hu; positivity
  linarith

lemma hmax_pos (P : Params) (hθ : 0 < P.τθ) (hu : 0 < P.τu) : 0 < hmax P := by
  unfold hmax; have := Real.sqrt_pos.mpr hθ; have := Real.sqrt_pos.mpr hu; positivity

lemma hfun_le_lin (P : Params) (α : ℝ) (hθ : 0 < P.τθ) (hu : 0 < P.τu) (hα : 0 ≤ α) :
    hfun P α ≤ α / P.τθ := by
  unfold hfun
  apply div_le_div_of_nonneg_left hα hθ; have : 0 ≤ α ^ 2 * P.τu := by positivity
  linarith

lemma hfun_le_inv (P : Params) (α : ℝ) (hθ : 0 < P.τθ) (hu : 0 < P.τu) (hα : 0 < α) :
    hfun P α ≤ 1 / (P.τu * α) := by
  unfold hfun
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hθ hα]

lemma R_lip_h (P : Params) (lam h1 h2 : ℝ) (hγ : 0 < P.γ) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH)
    (hZ : P.ZL ≤ P.ZH) (hl : 0 < lam) (h1p : 0 ≤ h1) (h2p : 0 ≤ h2) :
    |Rfun P lam h1 - Rfun P lam h2| ≤ (2 * P.γ * P.ZH / (P.ZH + P.ZL)) / lam * |h1 - h2| / 2 := by
  have hS : 0 < P.ZH + P.ZL := by linarith
  unfold Rfun
  have a1 := fr_lip _ _ (qfun_nonneg P P.ZH lam h1 hγ hZH hS hl h1p) (qfun_nonneg P P.ZH lam h2 hγ hZH hS hl h2p)
  have a2 := fr_lip _ _ (qfun_nonneg P P.ZL lam h1 hγ hZL hS hl h1p) (qfun_nonneg P P.ZL lam h2 hγ hZL hS hl h2p)
  have e : ∀ Z, qfun P Z lam h1 - qfun P Z lam h2 = (2 * P.γ * Z / (P.ZH + P.ZL)) / lam * (h1 - h2) := by
    intro Z; unfold qfun; ring
  rw [e, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * P.γ * P.ZH / (P.ZH + P.ZL) / lam)] at a1
  rw [e, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * P.γ * P.ZL / (P.ZH + P.ZL) / lam)] at a2
  have hk : 2 * P.γ * P.ZL / (P.ZH + P.ZL) / lam ≤ 2 * P.γ * P.ZH / (P.ZH + P.ZL) / lam := by
    apply div_le_div_of_nonneg_right _ hl.le
    apply div_le_div_of_nonneg_right _ hS.le
    nlinarith
  have a2' : |fr (qfun P P.ZL lam h1) - fr (qfun P P.ZL lam h2)| ≤
      2 * P.γ * P.ZH / (P.ZH + P.ZL) / lam * |h1 - h2| / 2 := by
    have := mul_le_mul_of_nonneg_right hk (abs_nonneg (h1 - h2)); linarith
  have : 1 / 2 * fr (qfun P P.ZH lam h1) + 1 / 2 * fr (qfun P P.ZL lam h1) -
      (1 / 2 * fr (qfun P P.ZH lam h2) + 1 / 2 * fr (qfun P P.ZL lam h2)) =
      1 / 2 * (fr (qfun P P.ZH lam h1) - fr (qfun P P.ZH lam h2)) +
      1 / 2 * (fr (qfun P P.ZL lam h1) - fr (qfun P P.ZL lam h2)) := by ring
  rw [this]
  calc _ ≤ |1 / 2 * (fr (qfun P P.ZH lam h1) - fr (qfun P P.ZH lam h2))| +
        |1 / 2 * (fr (qfun P P.ZL lam h1) - fr (qfun P P.ZL lam h2))| := abs_add_le _ _
    _ = 1 / 2 * |fr (qfun P P.ZH lam h1) - fr (qfun P P.ZH lam h2)| +
        1 / 2 * |fr (qfun P P.ZL lam h1) - fr (qfun P P.ZL lam h2)| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    _ ≤ _ := by linarith

lemma R_gap_h (P : Params) (lam h1 h2 Y : ℝ) (hγ : 0 < P.γ) (hZL : 0 < P.ZL) (hZ : P.ZL < P.ZH)
    (hl : 0 < lam) (hl1 : lam ≤ 1) (h1p : 0 ≤ h1) (h12 : h1 ≤ h2) (hY : qfun P P.ZH lam h2 ≤ Y) :
    (2 * P.γ * P.ZL / (P.ZH + P.ZL)) * (h2 - h1) / (2 * (1 + Y) * Real.sqrt (1 + Y))
      ≤ Rfun P lam h1 - Rfun P lam h2 := by
  have hZH : 0 < P.ZH := by linarith
  have hS : 0 < P.ZH + P.ZL := by linarith
  unfold Rfun
  have hq : ∀ Z, 0 < Z → Z ≤ P.ZH → qfun P Z lam h1 ≤ qfun P Z lam h2 ∧ qfun P Z lam h2 ≤ Y := by
    intro Z hZ0 hZle
    constructor
    · unfold qfun; apply div_le_div_of_nonneg_right _ hl.le
      apply mul_le_mul_of_nonneg_left h12 (by positivity)
    · refine le_trans ?_ hY
      unfold qfun; apply div_le_div_of_nonneg_right _ hl.le
      apply mul_le_mul_of_nonneg_right _ (le_trans h1p h12)
      apply div_le_div_of_nonneg_right _ hS.le; nlinarith
  obtain ⟨aH1, aH2⟩ := hq P.ZH hZH le_rfl
  obtain ⟨aL1, aL2⟩ := hq P.ZL hZL hZ.le
  have gH := fr_gap _ _ Y (qfun_nonneg P P.ZH lam h1 hγ hZH hS hl h1p) aH1 aH2
  have gL := fr_gap _ _ Y (qfun_nonneg P P.ZL lam h1 hγ hZL hS hl h1p) aL1 aL2
  have hY0 : 0 ≤ Y := le_trans (qfun_nonneg P P.ZH lam h2 hγ hZH hS hl (le_trans h1p h12)) hY
  have hD : 0 < 2 * (1 + Y) * Real.sqrt (1 + Y) := by
    have := Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 + Y); positivity
  have eZ : ∀ Z, qfun P Z lam h2 - qfun P Z lam h1 = (2 * P.γ * Z / (P.ZH + P.ZL)) * (h2 - h1) / lam := by
    intro Z; unfold qfun; ring
  rw [eZ] at gH gL
  have k1 : (2 * P.γ * P.ZL / (P.ZH + P.ZL)) * (h2 - h1) ≤ (2 * P.γ * P.ZL / (P.ZH + P.ZL)) * (h2 - h1) / lam := by
    rw [le_div_iff₀ hl]
    have : 0 ≤ (2 * P.γ * P.ZL / (P.ZH + P.ZL)) * (h2 - h1) := by
      have : 0 ≤ h2 - h1 := by linarith
      positivity
    nlinarith
  have k2 : (2 * P.γ * P.ZL / (P.ZH + P.ZL)) * (h2 - h1) ≤ (2 * P.γ * P.ZH / (P.ZH + P.ZL)) * (h2 - h1) / lam := by
    refine le_trans k1 ?_
    apply div_le_div_of_nonneg_right _ hl.le
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    apply div_le_div_of_nonneg_right _ hS.le; nlinarith
  have m1 := div_le_div_of_nonneg_right k1 hD.le
  have m2 := div_le_div_of_nonneg_right k2 hD.le
  linarith

lemma R_strictMono_lam (P : Params) (l1 l2 h : ℝ) (hγ : 0 < P.γ) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH)
    (hl1 : 0 < l1) (hl12 : l1 < l2) (hh : 0 < h) : Rfun P l1 h < Rfun P l2 h := by
  have hS : 0 < P.ZH + P.ZL := by linarith
  have hl2 : 0 < l2 := by linarith
  unfold Rfun
  have k : ∀ Z, 0 < Z → qfun P Z l2 h < qfun P Z l1 h := by
    intro Z hZ; unfold qfun
    apply div_lt_div_of_pos_left (by positivity) hl1 hl12
  have a := fr_strictAnti _ _ (qfun_nonneg P P.ZH l2 h hγ hZH hS hl2 hh.le) (k P.ZH hZH)
  have b := fr_strictAnti _ _ (qfun_nonneg P P.ZL l2 h hγ hZL hS hl2 hh.le) (k P.ZL hZL)
  linarith

lemma R_cont_lam (P : Params) (h : ℝ) (hγ : 0 < P.γ) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH) (hh : 0 ≤ h) :
    ContinuousOn (fun lam => Rfun P lam h) (Set.Ioi 0) := by
  have hS : 0 < P.ZH + P.ZL := by linarith
  unfold Rfun
  have cq : ∀ Z, 0 < Z → ContinuousOn (fun lam => qfun P Z lam h) (Set.Ioi 0) := by
    intro Z hZ; unfold qfun
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro l hl; exact (ne_of_gt hl)
  apply ContinuousOn.add
  · apply ContinuousOn.mul continuousOn_const
    exact fr_cont.comp (cq P.ZH hZH) (fun l hl => qfun_nonneg P P.ZH l h hγ hZH hS hl hh)
  · apply ContinuousOn.mul continuousOn_const
    exact fr_cont.comp (cq P.ZL hZL) (fun l hl => qfun_nonneg P P.ZL l h hγ hZL hS hl hh)

/-- the key estimate `|m - R(λ, h(α))|` -/
lemma m_R_est (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hx : 0 < x) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH) (hα : 0 < α) (hγ : 0 < P.γ)
    (hρH : 0 ≤ rhoH P τη x α) (hρL : 0 ≤ rhoL P τη x α) :
    |mfun P τη x α - Rfun P (lamOf P τη x α) (hfun P α)| ≤
      (qfun P P.ZH (lamOf P τη x α) (hfun P α) * |rhoH P τη x α - 1| +
        qfun P P.ZL (lamOf P τη x α) (hfun P α) * |rhoL P τη x α - 1|) / 4 := by
  have hS : 0 < P.ZH + P.ZL := by linarith
  have hl := lamOf_pos P τη x α hτ hu hγ (mul_pos hx hZH) (mul_pos hx hZL) hα
  have hh := hfun_nonneg P α hθ hu hα.le
  rw [mfun_eq P τη x α hθ hτ hu hx hZL hZH hα hγ]
  unfold Rfun
  set qH := qfun P P.ZH (lamOf P τη x α) (hfun P α)
  set qL := qfun P P.ZL (lamOf P τη x α) (hfun P α)
  have hqH : 0 ≤ qH := qfun_nonneg _ _ _ _ hγ hZH hS hl hh
  have hqL : 0 ≤ qL := qfun_nonneg _ _ _ _ hγ hZL hS hl hh
  have a1 := fr_lip (qH * rhoH P τη x α) qH (by positivity) hqH
  have a2 := fr_lip (qL * rhoL P τη x α) qL (by positivity) hqL
  have e1 : qH * rhoH P τη x α - qH = qH * (rhoH P τη x α - 1) := by ring
  have e2 : qL * rhoL P τη x α - qL = qL * (rhoL P τη x α - 1) := by ring
  rw [e1, abs_mul, abs_of_nonneg hqH] at a1
  rw [e2, abs_mul, abs_of_nonneg hqL] at a2
  have : 1 / 2 * fr (qH * rhoH P τη x α) + 1 / 2 * fr (qL * rhoL P τη x α) - (1 / 2 * fr qH + 1 / 2 * fr qL)
      = 1 / 2 * (fr (qH * rhoH P τη x α) - fr qH) + 1 / 2 * (fr (qL * rhoL P τη x α) - fr qL) := by ring
  rw [this]
  calc _ ≤ |1 / 2 * (fr (qH * rhoH P τη x α) - fr qH)| + |1 / 2 * (fr (qL * rhoL P τη x α) - fr qL)| :=
        abs_add_le _ _
    _ = 1 / 2 * |fr (qH * rhoH P τη x α) - fr qH| + 1 / 2 * |fr (qL * rhoL P τη x α) - fr qL| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    _ ≤ _ := by linarith

section Efacts
variable (P : Params) (C : ℝ → ℝ → ℝ) (c : ℝ)

lemma Efun_pos (l : ℝ) : 0 < Efun P C c l := Real.exp_pos _

lemma Efun_strictAnti (hγ : 0 < P.γ) (hβ1 : P.β < 1) (hCm : StrictMonoOn (C c) (Set.Ico 0 1))
    (l1 l2 : ℝ) (h1 : l1 ∈ Set.Ico (0:ℝ) 1) (h2 : l2 ∈ Set.Ico (0:ℝ) 1) (h12 : l1 < l2) :
    Efun P C c l2 < Efun P C c l1 := by
  unfold Efun
  apply Real.exp_lt_exp.mpr
  have := hCm h1 h2 h12
  have h1β : 0 < 1 - P.β := by linarith
  have : P.γ * C c l1 / (1 - P.β) < P.γ * C c l2 / (1 - P.β) := by
    apply div_lt_div_of_pos_right _ h1β; exact mul_lt_mul_of_pos_left this hγ
  linarith

lemma Efun_cont (hCc : ContinuousOn (C c) (Set.Ico 0 1)) :
    ContinuousOn (Efun P C c) (Set.Ico 0 1) := by
  unfold Efun
  apply Real.continuous_exp.comp_continuousOn
  apply ContinuousOn.neg
  apply ContinuousOn.div_const
  exact continuousOn_const.mul hCc

lemma Efun_zero (hC0 : C c 0 = 0) : Efun P C c 0 = 1 := by simp [Efun, hC0]

end Efacts

lemma rhoH_pos (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hx : 0 < x) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH) : 0 < rhoH P τη x α := by
  unfold rhoH r1
  have : 0 ≤ α ^ 2 * P.τu := by positivity
  have : 0 < P.τθ * τη / (P.τθ + τη) := by positivity
  positivity

lemma rhoL_pos (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hx : 0 < x) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH) : 0 < rhoL P τη x α := by
  unfold rhoL r1
  have : 0 ≤ α ^ 2 * P.τu := by positivity
  have : 0 < P.τθ * τη / (P.τθ + τη) := by positivity
  positivity

lemma rhoH_le_one (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hx : 0 < x) (hZL : 0 < P.ZL) (hZ : P.ZL < P.ZH) : rhoH P τη x α ≤ 1 := by
  have hZH : 0 < P.ZH := by linarith
  have hp : 0 ≤ α ^ 2 * P.τu := by positivity
  have h1 := r1_bounds P τη (α ^ 2 * P.τu) hθ hτ hp
  have h1' : r1 P τη (α ^ 2 * P.τu) ≤ 1 := by
    unfold r1
    have hk : 0 < P.τθ * τη / (P.τθ + τη) + α ^ 2 * P.τu := by positivity
    have e : (P.τθ + τη) * (P.τθ * τη / (P.τθ + τη) + α ^ 2 * P.τu) = P.τθ * τη + (P.τθ + τη) * (α ^ 2 * P.τu) := by
      field_simp
    rw [e, div_le_one (by positivity)]; nlinarith
  have h1p : 0 < r1 P τη (α ^ 2 * P.τu) := by
    unfold r1; have : 0 < P.τθ * τη / (P.τθ + τη) := by positivity
    positivity
  have h2 : (P.ZH + P.ZL) * (x * P.ZL + (α ^ 2 * P.τu + τη)) /
      ((α ^ 2 * P.τu + τη) * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [mul_pos hx hZL]
  unfold rhoH
  have h2p : 0 ≤ (P.ZH + P.ZL) * (x * P.ZL + (α ^ 2 * P.τu + τη)) /
      ((α ^ 2 * P.τu + τη) * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL) := by positivity
  nlinarith

lemma rho_err (P : Params) (τη x α D : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hx : 0 < x) (hZL : 0 < P.ZL) (hZ : P.ZL < P.ZH)
    (hD : x * P.ZH * (P.ZH - P.ZL) / (τη * (P.ZH + P.ZL)) ≤ D) :
    |rhoH P τη x α - 1| ≤ P.τθ / (P.τθ + τη) * (1 + D) + D ∧
    |rhoL P τη x α - 1| ≤ P.τθ / (P.τθ + τη) * (1 + D) + D := by
  have hZH : 0 < P.ZH := by linarith
  have hp : 0 ≤ α ^ 2 * P.τu := by positivity
  have h1 := r1_bounds P τη (α ^ 2 * P.τu) hθ hτ hp
  have hu' : τη ≤ α ^ 2 * P.τu + τη := by linarith
  have bH := r2_bounds x (α ^ 2 * P.τu + τη) P.ZH P.ZL τη hx hZH hZL hτ hu'
  have bL := r2_bounds x (α ^ 2 * P.τu + τη) P.ZL P.ZH τη hx hZL hZH hτ hu'
  have dH : x * P.ZL * |P.ZH - P.ZL| / (τη * (P.ZH + P.ZL)) ≤ D := by
    refine le_trans ?_ hD
    rw [abs_of_pos (by linarith)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    nlinarith
  have dL : x * P.ZH * |P.ZL - P.ZH| / (τη * (P.ZL + P.ZH)) ≤ D := by
    refine le_trans (le_of_eq ?_) hD
    rw [abs_sub_comm, abs_of_pos (by linarith), add_comm P.ZL P.ZH]
  have hD0 : 0 ≤ D := le_trans (by positivity) dH
  have hr10 : 0 ≤ P.τθ / (P.τθ + τη) := by positivity
  constructor
  · unfold rhoH
    refine le_trans (prod_bound _ _) ?_
    have := mul_le_mul h1 (by linarith : 1 + |(P.ZH + P.ZL) * (x * P.ZL + (α ^ 2 * P.τu + τη)) /
      ((α ^ 2 * P.τu + τη) * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL) - 1| ≤ 1 + D) (by positivity) hr10
    have e : (α ^ 2 * P.τu + τη) * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL
        = (α ^ 2 * P.τu + τη) * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL := rfl
    linarith
  · unfold rhoL
    refine le_trans (prod_bound _ _) ?_
    have := mul_le_mul h1 (by linarith : 1 + |(P.ZL + P.ZH) * (x * P.ZH + (α ^ 2 * P.τu + τη)) /
      ((α ^ 2 * P.τu + τη) * (P.ZL + P.ZH) + 2 * x * P.ZL * P.ZH) - 1| ≤ 1 + D) (by positivity) hr10
    linarith

/-- combined estimate -/
lemma m_R_bound (P : Params) (τη x α D Q : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hx : 0 < x) (hZL : 0 < P.ZL) (hZ : P.ZL < P.ZH) (hα : 0 < α) (hγ : 0 < P.γ)
    (hD : x * P.ZH * (P.ZH - P.ZL) / (τη * (P.ZH + P.ZL)) ≤ D)
    (hQ : qfun P P.ZH (lamOf P τη x α) (hfun P α) ≤ Q) :
    |mfun P τη x α - Rfun P (lamOf P τη x α) (hfun P α)| ≤
      Q * (P.τθ / (P.τθ + τη) * (1 + D) + D) / 2 := by
  have hZH : 0 < P.ZH := by linarith
  have hS : 0 < P.ZH + P.ZL := by linarith
  have e := m_R_est P τη x α hθ hτ hu hx hZL hZH hα hγ (rhoH_pos P τη x α hθ hτ hu hx hZL hZH).le
    (rhoL_pos P τη x α hθ hτ hu hx hZL hZH).le
  obtain ⟨eH, eL⟩ := rho_err P τη x α D hθ hτ hu hx hZL hZ hD
  have hl := lamOf_pos P τη x α hτ hu hγ (mul_pos hx hZH) (mul_pos hx hZL) hα
  have hh := hfun_nonneg P α hθ hu hα.le
  have qL_le : qfun P P.ZL (lamOf P τη x α) (hfun P α) ≤ Q := by
    refine le_trans ?_ hQ
    unfold qfun
    apply div_le_div_of_nonneg_right _ hl.le
    apply mul_le_mul_of_nonneg_right _ hh
    apply div_le_div_of_nonneg_right _ hS.le; nlinarith
  have hqH := qfun_nonneg P P.ZH (lamOf P τη x α) (hfun P α) hγ hZH hS hl hh
  have hqL := qfun_nonneg P P.ZL (lamOf P τη x α) (hfun P α) hγ hZL hS hl hh
  have hε0 : 0 ≤ P.τθ / (P.τθ + τη) * (1 + D) + D := le_trans (abs_nonneg _) eH
  have a := mul_le_mul hQ eH (abs_nonneg _) (le_trans hqH hQ)
  have b := mul_le_mul qL_le eL (abs_nonneg _) (le_trans hqH hQ)
  linarith

lemma sqrtH_eq (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hx : 0 < x) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH) (hα : 0 < α) (hγ : 0 < P.γ) :
    Real.sqrt (varH P τη x α / varU P τη α) =
      fr (qfun P P.ZH (lamOf P τη x α) (hfun P α) * rhoH P τη x α) := by
  have hp : 0 ≤ α ^ 2 * P.τu := by positivity
  have hU := cv_pos P τη (α ^ 2 * P.τu) hθ hτ hp
  have hH := cv_pos P τη (α ^ 2 * P.τu + x * P.ZH) hθ hτ (by positivity)
  simp only [varU, varH]
  rw [sqrt_ratio_eq _ _ hU hH]
  rw [y_eq_gen P τη x α P.ZH P.ZL hθ hτ hu hx hZH hZL hα hγ (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩)]
  unfold qfun hfun rhoH
  ring_nf

lemma crude_h (P : Params) (C : ℝ → ℝ → ℝ) (c τη x lam α lo e0 : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη)
    (hu : 0 < P.τu) (hγ : 0 < P.γ) (hβ1 : P.β < 1) (hZL : 0 < P.ZL) (hZ : P.ZL < P.ZH)
    (hx : 0 < x) (hα : 0 < α) (hlo : 0 < lo) (hl : lo ≤ lam) (he0 : 0 < e0)
    (h14 : Eq14 P τη x lam α) (h19 : (1 - P.β) * gain P τη x α = C c lam)
    (hE : Efun P C c lam ≤ e0) :
    lo * (1 / e0 ^ 2 - 1) / (2 * P.γ * P.ZH / (P.ZH + P.ZL)) ≤ hfun P α := by
  have hZH : 0 < P.ZH := by linarith
  have hS : 0 < P.ZH + P.ZL := by linarith
  have hxH := mul_pos hx hZH
  have hxL := mul_pos hx hZL
  have hm := feas_mfun P C c τη x lam α hθ hτ hu hγ hβ1 hxH.le hxL.le h19
  have hlam := (eq14_iff P τη x lam α hτ hu hxH hxL).mp h14
  have hp : 0 ≤ α ^ 2 * P.τu := by positivity
  have hU := cv_pos P τη (α ^ 2 * P.τu) hθ hτ hp
  have hHL : varH P τη x α ≤ varL P τη x α := by
    simp only [varH, varL]
    apply cv_anti_le P τη _ _ hθ hτ (by positivity)
    have := mul_le_mul_of_nonneg_left hZ.le hx.le; linarith
  have sHL : Real.sqrt (varH P τη x α / varU P τη α) ≤ Real.sqrt (varL P τη x α / varU P τη α) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hHL hU.le)
  have hmH : Real.sqrt (varH P τη x α / varU P τη α) ≤ mfun P τη x α := by unfold mfun; linarith
  rw [sqrtH_eq P τη x α hθ hτ hu hx hZL hZH hα hγ] at hmH
  have hl0 : 0 < lamOf P τη x α := lamOf_pos P τη x α hτ hu hγ hxH hxL hα
  have hh := hfun_nonneg P α hθ hu hα.le
  have hq := qfun_nonneg P P.ZH (lamOf P τη x α) (hfun P α) hγ hZH hS hl0 hh
  have hρ := rhoH_le_one P τη x α hθ hτ hu hx hZL hZ
  have hρ0 := (rhoH_pos P τη x α hθ hτ hu hx hZL hZH).le
  have hfr : fr (qfun P P.ZH (lamOf P τη x α) (hfun P α)) ≤ e0 := by
    have := fr_anti _ _ (mul_nonneg hq hρ0) (by nlinarith : qfun P P.ZH (lamOf P τη x α) (hfun P α) * rhoH P τη x α ≤ qfun P P.ZH (lamOf P τη x α) (hfun P α))
    linarith
  set q := qfun P P.ZH (lamOf P τη x α) (hfun P α) with hqdef
  have hq2 : 1 / e0 ^ 2 - 1 ≤ q := by
    unfold fr at hfr
    have hs : 0 < Real.sqrt (1 + q) := Real.sqrt_pos.mpr (by linarith)
    rw [div_le_iff₀ hs] at hfr
    have h2 : 1 ≤ e0 ^ 2 * (1 + q) := by
      have := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + q)
      nlinarith [mul_self_nonneg (e0 * Real.sqrt (1 + q))]
    rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have hq3 : q = (2 * P.γ * P.ZH / (P.ZH + P.ZL)) * hfun P α / lam := by
    rw [hqdef, ← hlam]; unfold qfun; ring
  have hk : 0 < 2 * P.γ * P.ZH / (P.ZH + P.ZL) := by positivity
  rw [div_le_iff₀ hk]
  have hlam0 : 0 < lam := lt_of_lt_of_le hlo hl
  have : (1 / e0 ^ 2 - 1) * lam ≤ (2 * P.γ * P.ZH / (P.ZH + P.ZL)) * hfun P α := by
    have := mul_le_mul_of_nonneg_right hq2 hlam0.le
    rw [hq3] at this
    rw [div_mul_cancel₀ _ hlam0.ne'] at this
    exact this
  rcases le_or_gt 0 (1 / e0 ^ 2 - 1) with h | h
  · have := mul_le_mul_of_nonneg_left hl h
    nlinarith
  · have : lo * (1 / e0 ^ 2 - 1) < 0 := mul_neg_of_pos_of_neg hlo h
    have : 0 ≤ hfun P α * (2 * P.γ * P.ZH / (P.ZH + P.ZL)) := by positivity
    linarith

lemma eq14_key (P : Params) (τη x lam α : ℝ) (hτ : 0 < τη) (hu : 0 < P.τu) (hγ : 0 < P.γ)
    (hZL : 0 < P.ZL) (hZ : P.ZL < P.ZH) (hx : 0 < x) (hlam : 0 < lam) (hα : 0 < α)
    (h14 : Eq14 P τη x lam α) :
    τη * (x - 2 * α * P.γ / (lam * (P.ZH + P.ZL))) ≤
        2 * α * P.γ / (lam * (P.ZH + P.ZL)) * (x * P.ZH + P.τu * α ^ 2) ∧
    -(x * (x * P.ZL * (P.ZH - P.ZL)) / (P.ZH + P.ZL)) ≤ τη * (x - 2 * α * P.γ / (lam * (P.ZH + P.ZL))) := by
  have hZH : 0 < P.ZH := by linarith
  have hS : 0 < P.ZH + P.ZL := by linarith
  have hΔ : 0 < P.ZH - P.ZL := by linarith
  set S := P.ZH + P.ZL with hSdef
  set Q := P.τu * α ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set x0 := 2 * α * P.γ / (lam * S) with hx0
  have hx0pos : 0 < x0 := by positivity
  have hD : 0 < x * P.ZL + Q + τη := by positivity
  set r := x * P.ZL * (P.ZH - P.ZL) / (x * P.ZL + Q + τη) with hr
  have hr0 : 0 ≤ r := by positivity
  have hrτ : τη * r ≤ x * P.ZL * (P.ZH - P.ZL) := by
    rw [hr, mul_div_assoc', div_le_iff₀ hD]
    have : 0 ≤ x * P.ZL * (P.ZH - P.ZL) := by positivity
    have : 0 ≤ x * P.ZL + Q := by positivity
    nlinarith [mul_nonneg ‹0 ≤ x * P.ZL * (P.ZH - P.ZL)› this]
  have h14' : P.γ * α * (x * P.ZH + Q + τη) - 1 / 2 * x * lam * τη * (S + r) = 0 := by
    unfold Eq14 at h14; rw [hr, hSdef, hQ]; exact h14
  clear_value S Q x0
  have hkey : τη * (x - x0) = x0 * (x * P.ZH + Q) - x * (τη * r) / S := by
    have hx0' : x0 * (lam * S) = 2 * α * P.γ := by rw [hx0]; field_simp
    have e : x * (τη * r) / S * S = x * (τη * r) := div_mul_cancel₀ _ hS.ne'
    have hlS : lam * S ≠ 0 := by positivity
    apply mul_left_cancel₀ hlS
    linear_combination (-2) * h14' - (τη + x * P.ZH + Q) * hx0' + lam * e
  constructor
  · have : 0 ≤ x * (τη * r) / S := by positivity
    linarith
  · have : x * (τη * r) / S ≤ x * (x * P.ZL * (P.ZH - P.ZL)) / S := by
      apply div_le_div_of_nonneg_right _ hS.le
      exact mul_le_mul_of_nonneg_left hrτ hx.le
    have : 0 ≤ x0 * (x * P.ZH + Q) := by positivity
    linarith

lemma asIs_excl (P : Params) (C : ℝ → ℝ → ℝ) (c τη lam α lo e0 : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη)
    (hu : 0 < P.τu) (hγ : 0 < P.γ) (hβ1 : P.β < 1) (hlo : 0 < lo) (he0 : 0 < e0) (he1 : e0 < 1)
    (hT : P.γ ^ 2 / (P.τu * lo ^ 2 * (1 - e0 ^ 2)) < τη)
    (hl : lo ≤ lam) (hga : P.γ * α = lam * τη) (h19 : (1 - P.β) * gainAsIs P τη α = C c lam)
    (hE : Efun P C c lam ≤ e0) : False := by
  have h := feas_asIs P C c τη lam α hθ hτ hu hγ hβ1 h19
  have hp : 0 ≤ α ^ 2 * P.τu := by positivity
  have hU := cv_pos P τη (α ^ 2 * P.τu) hθ hτ hp
  simp only [varU] at h
  rw [← Real.sqrt_div' _ hU.le] at h
  rw [cv_alt P τη _ hθ hτ hp] at h
  set p := α ^ 2 * P.τu with hpdef
  have hk : 0 < P.τθ * τη / (P.τθ + τη) := by positivity
  have e : 1 / (P.τθ + τη) / ((τη + p) / ((P.τθ + τη) * (P.τθ * τη / (P.τθ + τη) + p)))
      = (P.τθ * τη / (P.τθ + τη) + p) / (τη + p) := by
    field_simp
  rw [e] at h
  have hα : α = lam * τη / P.γ := by field_simp; linarith
  have hlam0 : 0 < lam := lt_of_lt_of_le hlo hl
  have hpbig : P.τu * lo ^ 2 * τη ^ 2 / P.γ ^ 2 ≤ p := by
    rw [hpdef, hα, div_le_iff₀ (by positivity)]
    have : lo ^ 2 ≤ lam ^ 2 := by nlinarith
    have e2 : (lam * τη / P.γ) ^ 2 * P.τu * P.γ ^ 2 = P.τu * lam ^ 2 * τη ^ 2 := by field_simp
    rw [e2]
    have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ P.τu * τη ^ 2)
    nlinarith
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hpbig
  -- (k+p)/(τη+p) ≥ p/(τη+p) > e0^2
  have h1 : e0 ^ 2 < p / (τη + p) := by
    have h1e : 0 < 1 - e0 ^ 2 := by nlinarith
    have hden : 0 < P.τu * lo ^ 2 * (1 - e0 ^ 2) := by positivity
    have h2 : P.γ ^ 2 < τη * (P.τu * lo ^ 2 * (1 - e0 ^ 2)) := by
      have := (div_lt_iff₀ hden).mp hT; linarith
    have a1 : (1 - e0 ^ 2) * (P.τu * lo ^ 2 * τη ^ 2 / P.γ ^ 2) ≤ (1 - e0 ^ 2) * p :=
      mul_le_mul_of_nonneg_left hpbig h1e.le
    have a2 : τη < (1 - e0 ^ 2) * (P.τu * lo ^ 2 * τη ^ 2 / P.γ ^ 2) := by
      rw [show (1 - e0 ^ 2) * (P.τu * lo ^ 2 * τη ^ 2 / P.γ ^ 2)
          = τη * (τη * (P.τu * lo ^ 2 * (1 - e0 ^ 2))) / P.γ ^ 2 by ring]
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    have a3 : e0 ^ 2 * τη ≤ τη := by nlinarith
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have h5 : p / (τη + p) ≤ (P.τθ * τη / (P.τθ + τη) + p) / (τη + p) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h6 : e0 < Real.sqrt ((P.τθ * τη / (P.τθ + τη) + p) / (τη + p)) := by
    rw [Real.lt_sqrt he0.le]; linarith
  linarith

noncomputable def Phi (P : Params) (C : ℝ → ℝ → ℝ) (c lam : ℝ) : ℝ :=
  Rfun P lam (hmax P) - Efun P C c lam

lemma Phi_strictMono (P : Params) (C : ℝ → ℝ → ℝ) (c : ℝ) (hθ : 0 < P.τθ) (hu : 0 < P.τu)
    (hγ : 0 < P.γ) (hβ1 : P.β < 1) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH)
    (hCm : StrictMonoOn (C c) (Set.Ico 0 1)) (l1 l2 : ℝ) (h1 : 0 < l1) (h2 : l2 < 1) (h12 : l1 < l2) :
    Phi P C c l1 < Phi P C c l2 := by
  unfold Phi
  have a := R_strictMono_lam P l1 l2 (hmax P) hγ hZL hZH h1 h12 (hmax_pos P hθ hu)
  have b := Efun_strictAnti P C c hγ hβ1 hCm l1 l2 ⟨h1.le, by linarith⟩ ⟨by linarith, h2⟩ h12
  linarith

lemma Phi_cont (P : Params) (C : ℝ → ℝ → ℝ) (c : ℝ) (hθ : 0 < P.τθ) (hu : 0 < P.τu)
    (hγ : 0 < P.γ) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH) (hCc : ContinuousOn (C c) (Set.Ico 0 1)) :
    ContinuousOn (Phi P C c) (Set.Ioo 0 1) := by
  unfold Phi
  apply ContinuousOn.sub
  · exact (R_cont_lam P (hmax P) hγ hZL hZH (hmax_pos P hθ hu).le).mono (fun l hl => hl.1)
  · exact (Efun_cont P C c hCc).mono (fun l hl => ⟨hl.1.le, hl.2⟩)

lemma fr_small (q : ℝ) (hq : 3 < q) : fr q < 1 / 2 := by
  unfold fr
  have : 2 < Real.sqrt (1 + q) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  rw [div_lt_iff₀ (by linarith)]; linarith

lemma Phi_root (P : Params) (C : ℝ → ℝ → ℝ) (c : ℝ) (hθ : 0 < P.τθ) (hu : 0 < P.τu)
    (hγ : 0 < P.γ) (hβ1 : P.β < 1) (hZL : 0 < P.ZL) (hZ : P.ZL < P.ZH)
    (hCc : ContinuousOn (C c) (Set.Ico 0 1)) (hCm : StrictMonoOn (C c) (Set.Ico 0 1))
    (hC0 : C c 0 = 0) (hCt : Tendsto (C c) (𝓝[<] 1) atTop) :
    ∃ lb ∈ Set.Ioo (0:ℝ) 1, Phi P C c lb = 0 := by
  have hZH : 0 < P.ZH := by linarith
  have hS : 0 < P.ZH + P.ZL := by linarith
  have hm := hmax_pos P hθ hu
  set κL := 2 * P.γ * P.ZL / (P.ZH + P.ZL) with hκL
  have hκL0 : 0 < κL := by positivity
  -- small λ: Φ < 0
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.mp
    ((Efun_cont P C c hCc) 0 ⟨le_rfl, zero_lt_one⟩) (1 / 2) (by norm_num)
  set la := min (min (δ / 2) (κL * hmax P / 4)) (1 / 2) with hla
  have hla0 : 0 < la := by positivity
  have hla1 : la ≤ 1 / 2 := min_le_right _ _
  have hlaδ : la ≤ δ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hlaκ : la ≤ κL * hmax P / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hPa : Phi P C c la < 0 := by
    unfold Phi
    have hE : 1 / 2 < Efun P C c la := by
      have := hδ' ⟨hla0.le, by linarith⟩ (by rw [Real.dist_eq, sub_zero, abs_of_pos hla0]; linarith)
      rw [Efun_zero P C c hC0, Real.dist_eq] at this
      have := (abs_lt.mp this).1; linarith
    have hqL : 3 < qfun P P.ZL la (hmax P) := by
      unfold qfun
      rw [lt_div_iff₀ hla0]
      have : 2 * P.γ * P.ZL / (P.ZH + P.ZL) * hmax P = κL * hmax P := rfl
      rw [this]; nlinarith
    have hqH : 3 < qfun P P.ZH la (hmax P) := by
      refine lt_of_lt_of_le hqL ?_
      unfold qfun
      apply div_le_div_of_nonneg_right _ hla0.le
      apply mul_le_mul_of_nonneg_right _ hm.le
      apply div_le_div_of_nonneg_right _ hS.le; nlinarith
    unfold Rfun
    have := fr_small _ hqL
    have := fr_small _ hqH
    linarith
  -- λ near 1: Φ > 0
  set r0 := Rfun P (1 / 2) (hmax P) with hr0
  have hr0pos : 0 < r0 := by
    rw [hr0]; unfold Rfun
    have := fr_pos (qfun P P.ZH (1 / 2) (hmax P)) (qfun_nonneg P _ _ _ hγ hZH hS (by norm_num) hm.le)
    have := fr_pos (qfun P P.ZL (1 / 2) (hmax P)) (qfun_nonneg P _ _ _ hγ hZL hS (by norm_num) hm.le)
    linarith
  have hEt : Tendsto (Efun P C c) (𝓝[<] 1) (𝓝 0) := by
    unfold Efun
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_neg_atTop_atBot.comp
    apply Tendsto.atTop_div_const (by linarith)
    exact Tendsto.const_mul_atTop hγ hCt
  have hlt : max la (1 / 2) < 1 := by
    rw [max_lt_iff]; constructor <;> linarith
  obtain ⟨lb', h1, h2⟩ := ((hEt.eventually (gt_mem_nhds hr0pos)).and (Ioo_mem_nhdsLT hlt)).exists
  have hlb'1 : 1 / 2 ≤ lb' := le_trans (le_max_right _ _) h2.1.le
  have hlalb : la < lb' := lt_of_le_of_lt (le_max_left _ _) h2.1
  have hPb : 0 < Phi P C c lb' := by
    unfold Phi
    have : r0 ≤ Rfun P lb' (hmax P) := by
      rcases eq_or_lt_of_le hlb'1 with h | h
      · rw [hr0, h]
      · exact (R_strictMono_lam P (1 / 2) lb' (hmax P) hγ hZL hZH (by norm_num) h hm).le
    linarith
  have hcont : ContinuousOn (Phi P C c) (Set.Icc la lb') :=
    (Phi_cont P C c hθ hu hγ hZL hZH hCc).mono (fun l hl => ⟨lt_of_lt_of_le hla0 hl.1, lt_of_le_of_lt hl.2 h2.2⟩)
  obtain ⟨lb, hlbI, hlb⟩ := intermediate_value_Icc hlalb.le hcont ⟨hPa.le, hPb.le⟩
  exact ⟨lb, ⟨lt_of_lt_of_le hla0 hlbI.1, lt_of_le_of_lt hlbI.2 h2.2⟩, hlb⟩

lemma EqC18_iff (P : Params) (C : ℝ → ℝ → ℝ) (c lam : ℝ) (hθ : 0 < P.τθ) (hu : 0 < P.τu)
    (hl : 0 < lam) : EqC18 P C c lam ↔ Phi P C c lam = 0 := by
  unfold EqC18 Phi Rfun Efun qfun hmax fr
  have e : ∀ Z : ℝ, Real.sqrt (1 / (P.γ * Z / (lam * (P.ZH + P.ZL) * Real.sqrt (P.τθ * P.τu)) + 1))
      = 1 / Real.sqrt (1 + 2 * P.γ * Z / (P.ZH + P.ZL) * (1 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu)) / lam) := by
    intro Z
    have hst : 0 < Real.sqrt P.τθ := Real.sqrt_pos.mpr hθ
    have hsu : 0 < Real.sqrt P.τu := Real.sqrt_pos.mpr hu
    have hq : P.γ * Z / (lam * (P.ZH + P.ZL) * Real.sqrt (P.τθ * P.τu))
        = 2 * P.γ * Z / (P.ZH + P.ZL) * (1 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu)) / lam := by
      rw [Real.sqrt_mul hθ.le]
      rcases eq_or_ne (P.ZH + P.ZL) 0 with h | h
      · rw [h]; simp
      · field_simp
    rw [hq, add_comm, one_div, one_div, Real.sqrt_inv, one_div]
  rw [e, e]
  set a := Real.exp (P.γ * C c lam / (1 - P.β))
  have ha : 0 < a := Real.exp_pos _
  have hneg : Real.exp (-(P.γ * C c lam / (1 - P.β))) = a⁻¹ := by rw [Real.exp_neg]
  rw [hneg]
  set f1 := 1 / Real.sqrt (1 + 2 * P.γ * P.ZH / (P.ZH + P.ZL) * (1 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu)) / lam)
  set f2 := 1 / Real.sqrt (1 + 2 * P.γ * P.ZL / (P.ZH + P.ZL) * (1 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu)) / lam)
  clear_value f1 f2 a
  have hi := mul_inv_cancel₀ ha.ne'
  constructor
  · intro h
    rw [sub_eq_zero]
    have : (1 / 2 * f1 + 1 / 2 * f2) = (1 / 2 * f1 + 1 / 2 * f2) * (a * a⁻¹) := by rw [hi, mul_one]
    rw [this]
    linear_combination a⁻¹ * h
  · intro h
    linear_combination a * h + hi

lemma gain_gt_of_m_lt (P : Params) (C : ℝ → ℝ → ℝ) (c τη x α l : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη)
    (hu : 0 < P.τu) (hγ : 0 < P.γ) (hβ1 : P.β < 1) (hxH : 0 ≤ x * P.ZH) (hxL : 0 ≤ x * P.ZL)
    (hm : mfun P τη x α < Efun P C c l) : C c l < (1 - P.β) * gain P τη x α := by
  rw [gain_mfun P τη x α hθ hτ hu hxH hxL]
  have hm0 := mfun_pos P τη x α hθ hτ hu hxH hxL
  have h1 : Real.log (mfun P τη x α) < -(P.γ * C c l / (1 - P.β)) := by
    unfold Efun at hm
    rwa [Real.log_lt_iff_lt_exp hm0]
  have h1β : 0 < 1 - P.β := by linarith
  have : C c l = (1 - P.β) * (-(1 / P.γ) * (-(P.γ * C c l / (1 - P.β)))) := by field_simp
  rw [this]
  apply mul_lt_mul_of_pos_left _ h1β
  have : 0 < 1 / P.γ := by positivity
  nlinarith

set_option maxHeartbeats 800000 in
lemma lower_construct (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (hC : IsCostFamily C)
    (c : ℝ) (hc : 0 < c) (lt : ℝ) (hlt0 : 0 < lt) (hlt1 : lt < 1) (hΦ : Phi P C c lt < 0) :
    ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη → ∃ x l a, Feasible P C c τη (.finite x) l a ∧ lt < l := by
  have hP' := hP
  obtain ⟨hθ, hu, hγ, hβ0, hβ1, hZL, hZ⟩ := hP
  obtain ⟨hCc, hCm, hC0, hCt⟩ := hC.1 c hc
  have hZH : 0 < P.ZH := by linarith
  have hS : 0 < P.ZH + P.ZL := by linarith
  have hΔ : 0 < P.ZH - P.ZL := by linarith
  have h1β : 0 < 1 - P.β := by linarith
  set S := P.ZH + P.ZL with hSdef
  set ainf := Real.sqrt (P.τθ / P.τu) with hainf
  have hainf0 : 0 < ainf := Real.sqrt_pos.mpr (by positivity)
  set x := 2 * P.γ * ainf / (lt * S) with hxdef
  have hx : 0 < x := by positivity
  have hxH := mul_pos hx hZH
  have hxL := mul_pos hx hZL
  set σ := Efun P C c lt - Rfun P lt (hmax P) with hσ
  have hσ0 : 0 < σ := by unfold Phi at hΦ; rw [hσ]; linarith
  set κH := 2 * P.γ * P.ZH / S with hκH
  have hκH0 : 0 < κH := by positivity
  set XU := x + x * (x * P.ZL * (P.ZH - P.ZL)) / S with hXU
  have hXU0 : 0 < XU := by positivity
  set AU := XU * lt * S / (2 * P.γ) with hAU
  set K := XU * (x * P.ZH + P.τu * AU ^ 2) + x * (x * P.ZL * (P.ZH - P.ZL)) / S with hK
  have hK0 : 0 ≤ K := by positivity
  set A1 := lt * S / (2 * P.γ) * K with hA1
  have hA10 : 0 ≤ A1 := by positivity
  have hst : 0 < Real.sqrt P.τθ := Real.sqrt_pos.mpr hθ
  have hsu : 0 < Real.sqrt P.τu := Real.sqrt_pos.mpr hu
  set c2 := P.τu / (2 * Real.sqrt P.τθ * Real.sqrt P.τu * P.τθ) with hc2
  have hc20 : 0 < c2 := by positivity
  set Q := κH * hmax P / lt with hQ
  have hQ0 : 0 < Q := by have := hmax_pos P hθ hu; positivity
  set D1 := x * P.ZH * (P.ZH - P.ZL) / S with hD1
  have hD10 : 0 < D1 := by positivity
  set M := κH / lt * (c2 * A1 ^ 2) / 2 + Q * (P.τθ * (1 + D1) + D1) / 2 with hM
  have hM0 : 0 ≤ M := by positivity
  clear_value M D1 Q c2 A1 K AU XU κH σ
  refine ⟨max 1 (M / σ + 1), fun τη hT => ?_⟩
  have hT1 : 1 ≤ τη := le_trans (le_max_left _ _) hT
  have hT2 : M / σ + 1 ≤ τη := le_trans (le_max_right _ _) hT
  have hτ : 0 < τη := by linarith
  -- α_t with lamOf x α_t = lt
  have Lcont := lamOf_cont P τη x hτ hu hxH hxL
  have L0 : lamOf P τη x 0 = 0 := by simp [lamOf]
  have hTg : 1 ≤ lamOf P τη x (τη / P.γ) := by
    have := lamOf_gt P τη x (τη / P.γ) hτ hu hγ hxH hxL (by positivity)
    have e : P.γ * (τη / P.γ) / τη = 1 := by field_simp
    rw [e] at this; exact this.le
  obtain ⟨αt, hαtI, hαt⟩ : ∃ αt ∈ Set.Icc (0:ℝ) (τη / P.γ), lamOf P τη x αt = lt :=
    intermediate_value_Icc (by positivity) Lcont.continuousOn ⟨by rw [L0]; exact hlt0.le, by linarith⟩
  have hαt0 : 0 < αt := by
    rcases eq_or_lt_of_le hαtI.1 with h | h
    · rw [← h, L0] at hαt; linarith
    · exact h
  have h14 : Eq14 P τη x lt αt := (eq14_iff P τη x lt αt hτ hu hxH hxL).mpr hαt.symm
  obtain ⟨kup, klo⟩ := eq14_key P τη x lt αt hτ hu hγ hZL hZ hx hlt0 hαt0 h14
  set x0 := 2 * αt * P.γ / (lt * S) with hx0
  have hx0pos : 0 < x0 := by positivity
  clear_value x0
  -- bounds
  have hx0U : x0 ≤ XU := by
    have : x * (x * P.ZL * (P.ZH - P.ZL)) / S / τη ≤ x * (x * P.ZL * (P.ZH - P.ZL)) / S :=
      div_le_self (by positivity) hT1
    have h2 : x0 - x ≤ x * (x * P.ZL * (P.ZH - P.ZL)) / S / τη := by
      rw [le_div_iff₀ hτ]; linarith
    rw [hXU]; linarith
  have hαtAU : αt ≤ AU := by
    have e : αt = x0 * lt * S / (2 * P.γ) := by rw [hx0]; field_simp
    rw [e, hAU]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_right hx0U (by positivity : (0:ℝ) ≤ lt * S)
    linarith
  have hKb : |τη * (x - x0)| ≤ K := by
    rw [abs_le]; constructor
    · have : 0 ≤ XU * (x * P.ZH + P.τu * AU ^ 2) := by positivity
      linarith
    · have h1 : x0 * (x * P.ZH + P.τu * αt ^ 2) ≤ XU * (x * P.ZH + P.τu * AU ^ 2) := by
        apply mul_le_mul hx0U _ (by positivity) hXU0.le
        have : αt ^ 2 ≤ AU ^ 2 := pow_le_pow_left₀ hαt0.le hαtAU 2
        have := mul_le_mul_of_nonneg_left this hu.le
        linarith
      have : 0 ≤ x * (x * P.ZL * (P.ZH - P.ZL)) / S := by positivity
      linarith
  have hαdiff : |αt - ainf| ≤ A1 / τη := by
    have e : αt - ainf = lt * S / (2 * P.γ) * (x0 - x) := by
      rw [hx0, hxdef]; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < lt * S / (2 * P.γ)), le_div_iff₀ hτ, hA1]
    have : |x0 - x| * τη ≤ K := by
      rw [abs_mul, abs_of_pos hτ] at hKb
      rw [abs_sub_comm]; linarith
    have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ lt * S / (2 * P.γ))
    linarith
  have hhgap : hmax P - hfun P αt ≤ c2 * A1 ^ 2 / τη := by
    rw [hmax_sub P αt hθ hu]
    have hsq : (αt - ainf) ^ 2 ≤ (A1 / τη) ^ 2 := by
      have := sq_abs (αt - ainf)
      rw [← this]
      exact pow_le_pow_left₀ (abs_nonneg _) hαdiff 2
    have hsq2 : (A1 / τη) ^ 2 ≤ A1 ^ 2 / τη := by
      rw [div_pow]
      apply div_le_div_of_nonneg_left (by positivity) hτ
      exact le_self_pow₀ hT1 (by norm_num)
    have hden : 2 * Real.sqrt P.τθ * Real.sqrt P.τu * P.τθ ≤
        2 * Real.sqrt P.τθ * Real.sqrt P.τu * (P.τθ + αt ^ 2 * P.τu) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_add_of_nonneg_right (by positivity)
    calc P.τu * (αt - ainf) ^ 2 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu * (P.τθ + αt ^ 2 * P.τu))
        ≤ P.τu * (αt - ainf) ^ 2 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu * P.τθ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = c2 * (αt - ainf) ^ 2 := by rw [hc2]; ring
      _ ≤ c2 * (A1 ^ 2 / τη) := mul_le_mul_of_nonneg_left (le_trans hsq hsq2) hc20.le
      _ = c2 * A1 ^ 2 / τη := by ring
  -- R comparison
  have hh0 := hfun_nonneg P αt hθ hu hαt0.le
  have hRlip := R_lip_h P lt (hfun P αt) (hmax P) hγ hZL hZH hZ.le hlt0 hh0 (hmax_pos P hθ hu).le
  have hhle := hfun_le P αt hθ hu
  rw [abs_sub_comm (hfun P αt) (hmax P), abs_of_nonneg (sub_nonneg.mpr hhle)] at hRlip
  have hR1 : Rfun P lt (hfun P αt) ≤ Rfun P lt (hmax P) + κH / lt * (c2 * A1 ^ 2 / τη) / 2 := by
    have := (abs_le.mp hRlip).2
    have h3 : 2 * P.γ * P.ZH / (P.ZH + P.ZL) / lt * (hmax P - hfun P αt) / 2 ≤
        κH / lt * (c2 * A1 ^ 2 / τη) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      rw [hκH]
      exact mul_le_mul_of_nonneg_left hhgap (by positivity)
    linarith
  -- m comparison
  have hDb : x * P.ZH * (P.ZH - P.ZL) / (τη * (P.ZH + P.ZL)) ≤ D1 / τη := by
    rw [hD1, div_div, mul_comm S τη]
  have hqb : qfun P P.ZH (lamOf P τη x αt) (hfun P αt) ≤ Q := by
    rw [hαt, hQ, hκH]; unfold qfun
    apply div_le_div_of_nonneg_right _ hlt0.le
    exact mul_le_mul_of_nonneg_left hhle (by positivity)
  have hmR := m_R_bound P τη x αt (D1 / τη) Q hθ hτ hu hx hZL hZ hαt0 hγ hDb hqb
  rw [hαt] at hmR
  have herr : Q * (P.τθ / (P.τθ + τη) * (1 + D1 / τη) + D1 / τη) / 2 ≤
      Q * (P.τθ * (1 + D1) + D1) / 2 / τη := by
    have a1 : P.τθ / (P.τθ + τη) ≤ P.τθ / τη := div_le_div_of_nonneg_left hθ.le hτ (by linarith)
    have a2 : D1 / τη ≤ D1 := div_le_self hD10.le hT1
    have a3 : P.τθ / (P.τθ + τη) * (1 + D1 / τη) ≤ P.τθ / τη * (1 + D1) :=
      mul_le_mul a1 (by linarith) (by positivity) (by positivity)
    have a4 : (P.τθ / (P.τθ + τη) * (1 + D1 / τη) + D1 / τη) ≤ (P.τθ * (1 + D1) + D1) / τη := by
      have : P.τθ / τη * (1 + D1) + D1 / τη = (P.τθ * (1 + D1) + D1) / τη := by field_simp
      linarith
    calc Q * (P.τθ / (P.τθ + τη) * (1 + D1 / τη) + D1 / τη) / 2
        ≤ Q * ((P.τθ * (1 + D1) + D1) / τη) / 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left a4 hQ0.le) (by norm_num)
      _ = Q * (P.τθ * (1 + D1) + D1) / 2 / τη := by ring
  have hMτ : M / τη < σ := by
    rw [div_lt_iff₀ hτ]
    have : M / σ < τη := by linarith
    rw [div_lt_iff₀ hσ0] at this; linarith
  have hm_lt : mfun P τη x αt < Efun P C c lt := by
    have := (abs_le.mp hmR).2
    have e : M / τη = κH / lt * (c2 * A1 ^ 2 / τη) / 2 + Q * (P.τθ * (1 + D1) + D1) / 2 / τη := by
      rw [hM]; ring
    linarith
  have hG := gain_gt_of_m_lt P C c τη x αt lt hθ hτ hu hγ hβ1 hxH.le hxL.le hm_lt
  -- the feasible pair at x
  obtain ⟨⟨l', a'⟩, hF, -⟩ := SkillData.GoldRush.unique_pair_of_clarity P hP' C hC c τη x hc hτ hx
  refine ⟨x, l', a', hF, ?_⟩
  obtain ⟨-, hl'0, hl'1, ha'0, h14', h19'⟩ := hF
  simp only at hl'0 hl'1 ha'0 h14' h19'
  have hl' := (eq14_iff P τη x l' a' hτ hu hxH hxL).mp h14'
  by_contra hcon
  push_neg at hcon
  have ha'le : a' ≤ αt := by
    by_contra h; push_neg at h
    have := lamOf_strictMono P τη x αt a' hτ hu hγ hxH hxL hαt0.le h
    rw [hαt, ← hl'] at this; linarith
  have g1 : gain P τη x αt ≤ gain P τη x a' := by
    rcases eq_or_lt_of_le ha'le with h | h
    · rw [h]
    · exact (gain_strictAnti P τη x a' αt hθ hτ hu hγ hxH hxL ha'0.le h).le
  have c1 : C c l' ≤ C c lt := hCm.monotoneOn ⟨hl'0.le, hl'1⟩ ⟨hlt0.le, hlt1⟩ hcon
  have := mul_le_mul_of_nonneg_left g1 h1β.le
  linarith

lemma profit_strict (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (c τη : ℝ)
    (hCm : StrictMonoOn (C c) (Set.Ico 0 1)) (hC0 : C c 0 = 0)
    (X X' : Clarity) (l a l' a' : ℝ) (hF : Feasible P C c τη X l a) (hF' : Feasible P C c τη X' l' a')
    (hl0 : 0 < l) (hl1 : l < 1) (hl'1 : l' < 1) (hll' : l < l') :
    profit P τη X l a < profit P τη X' l' a' := by
  have hP' := hP
  obtain ⟨hθ, hu, hγ, hβ0, hβ1, hZL, hZ⟩ := hP
  rw [SkillData.GoldRush.eq_C5 P hP' C c τη X l a hF, SkillData.GoldRush.eq_C5 P hP' C c τη X' l' a' hF']
  have h1β : 0 < 1 - P.β := by linarith
  have c1 : C c l < C c l' := hCm ⟨hl0.le, hl1⟩ ⟨by linarith, hl'1⟩ hll'
  have c0 : 0 ≤ C c l := by rw [← hC0]; exact hCm.monotoneOn ⟨le_rfl, zero_lt_one⟩ ⟨hl0.le, hl1⟩ hl0.le
  apply div_lt_div_of_pos_right _ h1β
  have : l * C c l < l' * C c l' := by nlinarith
  nlinarith

lemma alpha_hi_aux (hl u α : ℝ) (hu : 0 < u) (hα : 0 < α) (hl0 : 0 < hl) (h : hl ≤ 1 / (u * α)) :
    α ≤ 1 / (u * hl) := by
  rw [le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma x_bound_aux (τη x x0 X0 ZH Qa Qhi : ℝ) (kup : τη * (x - x0) ≤ x0 * (x * ZH + Qa))
    (hx0 : x0 ≤ X0) (hx0p : 0 < x0) (hQa : Qa ≤ Qhi) (hQa0 : 0 ≤ Qa) (hT1 : 1 ≤ τη)
    (hT2 : 2 * X0 * ZH ≤ τη) (hx : 0 < x) (hZH : 0 < ZH) : x ≤ 2 * X0 * (1 + Qhi) := by
  have hτ : 0 < τη := by linarith
  have hX0 : 0 < X0 := by linarith
  have h1 : x0 * x * ZH * 2 ≤ τη * x := by
    have : x0 * ZH * 2 ≤ τη := by nlinarith
    nlinarith
  have h2 : x0 * Qa ≤ τη * (X0 * Qhi) := by
    have := mul_le_mul hx0 hQa hQa0 hX0.le
    have : X0 * Qhi ≤ τη * (X0 * Qhi) := le_mul_of_one_le_left (by nlinarith) hT1
    linarith
  have h3 : τη * (x / 2) ≤ τη * (X0 * (1 + Qhi)) := by nlinarith
  have h4 := le_of_mul_le_mul_left h3 hτ
  linarith

lemma q_bound_aux (k h hm lam lo : ℝ) (hk : 0 ≤ k) (hh : h ≤ hm) (hh0 : 0 ≤ h) (hlo : 0 < lo)
    (hl : lo ≤ lam) : k * h / lam ≤ k * hm / lo := by
  have hlam : 0 < lam := lt_of_lt_of_le hlo hl
  rw [div_le_div_iff₀ hlam hlo]
  have a := mul_le_mul_of_nonneg_left hh hk
  have hm0 : 0 ≤ hm := le_trans hh0 hh
  have := mul_le_mul a hl hlo.le (by positivity)
  linarith

set_option maxHeartbeats 800000 in
theorem main_asym (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (hC : IsCostFamily C)
    (c : ℝ) (hc : 0 < c) (lb : ℝ) (hlb : lb ∈ Set.Ioo (0:ℝ) 1) (hΦ : Phi P C c lb = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη →
      ∀ (X : Clarity) (lam α : ℝ), IsEquilibrium P C c τη X lam α →
        (∃ x, X = .finite x) ∧ |lam - lb| < ε ∧ |α - Real.sqrt (P.τθ / P.τu)| < ε := by
  intro ε hε
  have hP' := hP
  obtain ⟨hθ, hu, hγ, hβ0, hβ1, hZL, hZ⟩ := hP
  obtain ⟨hCc, hCm, hC0, hCt⟩ := hC.1 c hc
  have hZH : 0 < P.ZH := by linarith
  have hS : 0 < P.ZH + P.ZL := by linarith
  have hΔ : 0 < P.ZH - P.ZL := by linarith
  have h1β : 0 < 1 - P.β := by linarith
  obtain ⟨hlb0, hlb1⟩ := hlb
  have hm := hmax_pos P hθ hu
  have hst : 0 < Real.sqrt P.τθ := Real.sqrt_pos.mpr hθ
  have hsu : 0 < Real.sqrt P.τu := Real.sqrt_pos.mpr hu
  -- constants
  set lo := lb / 2 with hlo
  have hlo0 : 0 < lo := by positivity
  have hlo1 : lo < 1 := by linarith
  set e0 := Efun P C c lo with he0
  have he00 : 0 < e0 := Efun_pos P C c lo
  have he01 : e0 < 1 := by
    have := Efun_strictAnti P C c hγ hβ1 hCm 0 lo ⟨le_rfl, zero_lt_one⟩ ⟨hlo0.le, hlo1⟩ hlo0
    rw [Efun_zero P C c hC0] at this; exact this
  set κH := 2 * P.γ * P.ZH / (P.ZH + P.ZL) with hκH
  set κL := 2 * P.γ * P.ZL / (P.ZH + P.ZL) with hκL
  have hκH0 : 0 < κH := by positivity
  have hκL0 : 0 < κL := by positivity
  set hlo_ := lo * (1 / e0 ^ 2 - 1) / κH with hhlo
  have hhlo0 : 0 < hlo_ := by
    have : 1 < 1 / e0 ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    have : 0 < 1 / e0 ^ 2 - 1 := by linarith
    positivity
  set ahi := 1 / (P.τu * hlo_) with hahi
  have hahi0 : 0 < ahi := by positivity
  set X0 := 2 * P.γ * ahi / (lo * (P.ZH + P.ZL)) with hX0
  have hX00 : 0 < X0 := by positivity
  set XB := 2 * X0 * (1 + P.τu * ahi ^ 2) with hXB
  have hXB0 : 0 < XB := by positivity
  set Q := κH * hmax P / lo with hQ
  have hQ0 : 0 < Q := by positivity
  set D1 := XB * P.ZH * (P.ZH - P.ZL) / (P.ZH + P.ZL) with hD1
  have hD10 : 0 < D1 := by positivity
  set MU := Q * (P.τθ * (1 + D1) + D1) / 2 with hMU
  have hMU0 : 0 < MU := by positivity
  set η := P.τu * ε ^ 2 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu * (P.τθ + ahi ^ 2 * P.τu)) with hη
  have hη0 : 0 < η := by positivity
  set μ := κL * η / (2 * (1 + Q) * Real.sqrt (1 + Q)) with hμ
  have hμ0 : 0 < μ := by
    have := Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 + Q); positivity
  -- ν from continuity of Φ at lb
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.mp
    ((Phi_cont P C c hθ hu hγ hZL hZH hCc) lb ⟨hlb0, hlb1⟩) (μ / 2) (by positivity)
  set ν := min (min (ε / 2) (lb / 2)) (δ / 2) with hν
  have hν0 : 0 < ν := by positivity
  have hνε : ν < ε := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have hνlb : ν ≤ lb / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hνδ : ν ≤ δ / 2 := min_le_right _ _
  set lt := lb - ν with hlt
  have hlt0 : 0 < lt := by linarith
  have hlt1 : lt < 1 := by linarith
  have hltlo : lo ≤ lt := by linarith
  have hΦlt : Phi P C c lt < 0 := by
    have := Phi_strictMono P C c hθ hu hγ hβ1 hZL hZH hCm lt lb hlt0 hlb1 (by linarith)
    linarith
  have hΦlt2 : -(μ / 2) < Phi P C c lt := by
    have := hδ' ⟨hlt0, hlt1⟩ (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, hΦ, sub_zero] at this
    linarith [(abs_lt.mp this).1]
  obtain ⟨TL, hTL⟩ := lower_construct P hP' C hC c hc lt hlt0 hlt1 hΦlt
  -- upper threshold for λ
  set φp := if h : lb + ε < 1 then Phi P C c (lb + ε) else 1 with hφp
  have hφp0 : 0 < φp := by
    rw [hφp]; split_ifs with h
    · have := Phi_strictMono P C c hθ hu hγ hβ1 hZL hZH hCm lb (lb + ε) hlb0 h (by linarith)
      linarith
    · norm_num
  set Tas := P.γ ^ 2 / (P.τu * lo ^ 2 * (1 - e0 ^ 2)) + 1 with hTas
  clear_value Tas φp lt ν μ η MU D1 Q XB X0 ahi hlo_ κL κH e0 lo
  refine ⟨max (max (max 1 (2 * X0 * P.ZH)) (max TL Tas)) (max (2 * MU / μ + 1) (MU / φp + 1)), ?_⟩
  intro τη hT X lam α hE
  have hT1 : 1 ≤ τη := by
    have := le_max_left (max (max 1 (2 * X0 * P.ZH)) (max TL Tas)) (max (2 * MU / μ + 1) (MU / φp + 1))
    have := le_max_left (max 1 (2 * X0 * P.ZH)) (max TL Tas)
    have := le_max_left 1 (2 * X0 * P.ZH)
    linarith
  have hT2 : 2 * X0 * P.ZH ≤ τη := by
    have := le_max_left (max (max 1 (2 * X0 * P.ZH)) (max TL Tas)) (max (2 * MU / μ + 1) (MU / φp + 1))
    have := le_max_left (max 1 (2 * X0 * P.ZH)) (max TL Tas)
    have := le_max_right 1 (2 * X0 * P.ZH)
    linarith
  have hTL' : TL ≤ τη := by
    have := le_max_left (max (max 1 (2 * X0 * P.ZH)) (max TL Tas)) (max (2 * MU / μ + 1) (MU / φp + 1))
    have := le_max_right (max 1 (2 * X0 * P.ZH)) (max TL Tas)
    have := le_max_left TL Tas
    linarith
  have hTas' : Tas ≤ τη := by
    have := le_max_left (max (max 1 (2 * X0 * P.ZH)) (max TL Tas)) (max (2 * MU / μ + 1) (MU / φp + 1))
    have := le_max_right (max 1 (2 * X0 * P.ZH)) (max TL Tas)
    have := le_max_right TL Tas
    linarith
  have hTμ : 2 * MU / μ + 1 ≤ τη := by
    have := le_max_right (max (max 1 (2 * X0 * P.ZH)) (max TL Tas)) (max (2 * MU / μ + 1) (MU / φp + 1))
    have := le_max_left (2 * MU / μ + 1) (MU / φp + 1)
    linarith
  have hTφ : MU / φp + 1 ≤ τη := by
    have := le_max_right (max (max 1 (2 * X0 * P.ZH)) (max TL Tas)) (max (2 * MU / μ + 1) (MU / φp + 1))
    have := le_max_right (2 * MU / μ + 1) (MU / φp + 1)
    linarith
  have hτ : 0 < τη := by linarith
  obtain ⟨hF, hopt⟩ := hE
  have hlam1 : lam < 1 := by cases X with
    | finite x => exact hF.2.2.1
    | asIs => exact hF.2.1
  have hlam0 : 0 < lam := by cases X with
    | finite x => exact hF.2.1
    | asIs => exact hF.1
  -- lower bound λ > lt
  have hlamlt : lt < lam := by
    obtain ⟨x', l', a', hF', hl'⟩ := hTL τη hTL'
    have hl'1 : l' < 1 := hF'.2.2.1
    by_contra hcon; push_neg at hcon
    rcases eq_or_lt_of_le (le_trans hcon hl'.le) with h | h
    · linarith
    · have := profit_strict P hP' C c τη hCm hC0 X (.finite x') lam α l' a' hF hF' hlam0 hlam1 hl'1 h
      have := hopt _ _ _ hF'
      linarith
  have hlamlo : lo ≤ lam := by linarith
  have hElam : Efun P C c lam ≤ e0 := by
    rw [he0]
    rcases eq_or_lt_of_le hlamlo with h | h
    · rw [← h]
    · exact (Efun_strictAnti P C c hγ hβ1 hCm lo lam ⟨hlo0.le, hlo1⟩ ⟨hlam0.le, hlam1⟩ h).le
  -- not as is
  cases X with
  | asIs =>
    exfalso
    obtain ⟨-, -, hα, hga, h19⟩ := hF
    exact asIs_excl P C c τη lam α lo e0 hθ hτ hu hγ hβ1 hlo0 he00 he01 (by linarith) hlamlo hga h19 hElam
  | finite x =>
    obtain ⟨hx, -, -, hα, h14, h19⟩ := hF
    refine ⟨⟨x, rfl⟩, ?_⟩
    have hxH := mul_pos hx hZH
    have hxL := mul_pos hx hZL
    have hl := (eq14_iff P τη x lam α hτ hu hxH hxL).mp h14
    -- α ≤ ahi
    have hh := crude_h P C c τη x lam α lo e0 hθ hτ hu hγ hβ1 hZL hZ hx hα hlo0 hlamlo he00 h14 h19 hElam
    have hh' : hlo_ ≤ hfun P α := by rw [hhlo, hκH]; exact hh
    have hαhi : α ≤ ahi := by
      rw [hahi]
      exact alpha_hi_aux hlo_ P.τu α hu hα hhlo0 (le_trans hh' (hfun_le_inv P α hθ hu hα))
    -- x ≤ XB
    obtain ⟨kup, -⟩ := eq14_key P τη x lam α hτ hu hγ hZL hZ hx hlam0 hα h14
    have hx0 : 2 * α * P.γ / (lam * (P.ZH + P.ZL)) ≤ X0 := by
      rw [hX0, div_le_div_iff₀ (by positivity) (by positivity)]
      have a1 : 2 * α * P.γ ≤ 2 * P.γ * ahi := by
        have := mul_le_mul_of_nonneg_left hαhi (by positivity : (0:ℝ) ≤ 2 * P.γ); linarith
      have a2 : lo * (P.ZH + P.ZL) ≤ lam * (P.ZH + P.ZL) := mul_le_mul_of_nonneg_right hlamlo hS.le
      exact mul_le_mul a1 a2 (by positivity) (by positivity)
    have hxB : x ≤ XB := by
      have hQa : P.τu * α ^ 2 ≤ P.τu * ahi ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hα.le hαhi 2) hu.le
      rw [hXB]
      exact x_bound_aux τη x _ X0 P.ZH _ _ kup hx0 (by positivity) hQa (by positivity) hT1 hT2 hx hZH
    -- the estimate
    have hDb : x * P.ZH * (P.ZH - P.ZL) / (τη * (P.ZH + P.ZL)) ≤ D1 / τη := by
      rw [hD1, div_div, mul_comm (P.ZH + P.ZL) τη]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hΔ.le
      exact mul_le_mul_of_nonneg_right hxB hZH.le
    have hhle := hfun_le P α hθ hu
    have hh0 := hfun_nonneg P α hθ hu hα.le
    have hqb : qfun P P.ZH (lamOf P τη x α) (hfun P α) ≤ Q := by
      rw [← hl, hQ, hκH]; unfold qfun
      exact q_bound_aux _ _ _ _ _ (by positivity) hhle hh0 hlo0 hlamlo
    have hmR := m_R_bound P τη x α (D1 / τη) Q hθ hτ hu hx hZL hZ hα hγ hDb hqb
    rw [← hl, feas_mfun P C c τη x lam α hθ hτ hu hγ hβ1 hxH.le hxL.le h19] at hmR
    have herr : Q * (P.τθ / (P.τθ + τη) * (1 + D1 / τη) + D1 / τη) / 2 ≤ MU / τη := by
      have a1 : P.τθ / (P.τθ + τη) ≤ P.τθ / τη := div_le_div_of_nonneg_left hθ.le hτ (by linarith)
      have a2 : D1 / τη ≤ D1 := div_le_self hD10.le hT1
      have a3 : P.τθ / (P.τθ + τη) * (1 + D1 / τη) ≤ P.τθ / τη * (1 + D1) :=
        mul_le_mul a1 (by linarith) (by positivity) (by positivity)
      have a4 : (P.τθ / (P.τθ + τη) * (1 + D1 / τη) + D1 / τη) ≤ (P.τθ * (1 + D1) + D1) / τη := by
        have : P.τθ / τη * (1 + D1) + D1 / τη = (P.τθ * (1 + D1) + D1) / τη := by field_simp
        linarith
      calc Q * (P.τθ / (P.τθ + τη) * (1 + D1 / τη) + D1 / τη) / 2
          ≤ Q * ((P.τθ * (1 + D1) + D1) / τη) / 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left a4 hQ0.le) (by norm_num)
        _ = MU / τη := by rw [hMU]; ring
    have hEm : Rfun P lam (hfun P α) - MU / τη ≤ Efun P C c lam := by
      have := (abs_le.mp hmR).1; linarith
    -- R(λ, h(α)) - R(λ, hmax) ≥ κL (hmax - h)/(2(1+Q)√(1+Q))
    have hqmax : qfun P P.ZH lam (hmax P) ≤ Q := by
      rw [hQ, hκH]; unfold qfun
      exact q_bound_aux _ _ _ _ _ (by positivity) le_rfl hm.le hlo0 hlamlo
    have hgap := R_gap_h P lam (hfun P α) (hmax P) Q hγ hZL hZ hlam0 hlam1.le hh0 hhle hqmax
    rw [← hκL] at hgap
    have hgap0 : 0 ≤ κL * (hmax P - hfun P α) / (2 * (1 + Q) * Real.sqrt (1 + Q)) := by
      have := Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 + Q)
      have : 0 ≤ hmax P - hfun P α := by linarith
      positivity
    have hΦup : Phi P C c lam ≤ MU / τη := by unfold Phi; linarith
    have hMUμ : MU / τη < μ / 2 := by
      rw [div_lt_iff₀ hτ]
      have : 2 * MU / μ < τη := by linarith
      rw [div_lt_iff₀ hμ0] at this; linarith
    constructor
    · -- |λ - lb| < ε
      rw [abs_lt]; constructor
      · linarith
      · by_contra hcon0; push_neg at hcon0
        have hcon : lb + ε ≤ lam := by linarith
        have hlbε : lb + ε < 1 := by linarith
        have hφ : φp = Phi P C c (lb + ε) := by rw [hφp, dif_pos hlbε]
        have h1 : Phi P C c (lb + ε) ≤ Phi P C c lam := by
          rcases eq_or_lt_of_le hcon with h | h
          · rw [h]
          · exact (Phi_strictMono P C c hθ hu hγ hβ1 hZL hZH hCm _ _ (by linarith) hlam1 h).le
        have h2 : MU / τη < φp := by
          rw [div_lt_iff₀ hτ]
          have : MU / φp < τη := by linarith
          rw [div_lt_iff₀ hφp0] at this; linarith
        linarith
    · -- |α - α∞| < ε
      by_contra hcon; push_neg at hcon
      have hηle : η ≤ hmax P - hfun P α := by
        rw [hmax_sub P α hθ hu, hη]
        have hsq : ε ^ 2 ≤ (α - Real.sqrt (P.τθ / P.τu)) ^ 2 := by
          rw [← sq_abs (α - Real.sqrt (P.τθ / P.τu))]
          exact pow_le_pow_left₀ hε.le hcon 2
        have hden : 2 * Real.sqrt P.τθ * Real.sqrt P.τu * (P.τθ + α ^ 2 * P.τu) ≤
            2 * Real.sqrt P.τθ * Real.sqrt P.τu * (P.τθ + ahi ^ 2 * P.τu) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hα.le hαhi 2) hu.le
          linarith
        calc P.τu * ε ^ 2 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu * (P.τθ + ahi ^ 2 * P.τu))
            ≤ P.τu * (α - Real.sqrt (P.τθ / P.τu)) ^ 2 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu * (P.τθ + ahi ^ 2 * P.τu)) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hu.le) (by positivity)
          _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      have hμle : μ ≤ κL * (hmax P - hfun P α) / (2 * (1 + Q) * Real.sqrt (1 + Q)) := by
        rw [hμ]
        apply div_le_div_of_nonneg_right _ (by have := Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 + Q); positivity)
        exact mul_le_mul_of_nonneg_left hηle hκL0.le
      have hΦdown : Phi P C c lam ≤ MU / τη - μ := by unfold Phi; linarith
      have hmono : Phi P C c lt < Phi P C c lam :=
        Phi_strictMono P C c hθ hu hγ hβ1 hZL hZH hCm lt lam hlt0 hlam1 hlamlt
      linarith only [hΦlt2, hmono, hΦdown, hMUμ]

end GRAsym



namespace GRAsym

lemma lb_anti (P : Params) (C : ℝ → ℝ → ℝ) (hC : IsCostFamily C) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hc : c₁ < c₂) (hθ : 0 < P.τθ) (hu : 0 < P.τu) (hγ : 0 < P.γ) (hβ1 : P.β < 1)
    (hZL : 0 < P.ZL) (hZH : 0 < P.ZH)
    (l₁ l₂ : ℝ) (h₁ : l₁ ∈ Set.Ioo (0:ℝ) 1) (h₂ : l₂ ∈ Set.Ioo (0:ℝ) 1)
    (hΦ₁ : Phi P C c₁ l₁ = 0) (hΦ₂ : Phi P C c₂ l₂ = 0) : l₂ < l₁ := by
  have hc₂ : 0 < c₂ := by linarith
  obtain ⟨-, hCm₂, -, -⟩ := hC.1 c₂ hc₂
  by_contra hcon; push_neg at hcon
  have hCc : C c₁ l₁ < C c₂ l₁ := hC.2 l₁ h₁ hc₁ hc₂ hc
  have hE1 : Efun P C c₂ l₁ < Efun P C c₁ l₁ := by
    unfold Efun
    apply Real.exp_lt_exp.mpr
    have h1β : 0 < 1 - P.β := by linarith
    have : P.γ * C c₁ l₁ / (1 - P.β) < P.γ * C c₂ l₁ / (1 - P.β) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hCc hγ) h1β
    linarith
  have hE2 : Efun P C c₂ l₂ ≤ Efun P C c₂ l₁ := by
    rcases eq_or_lt_of_le hcon with h | h
    · rw [h]
    · exact (Efun_strictAnti P C c₂ hγ hβ1 hCm₂ l₁ l₂ ⟨h₁.1.le, h₁.2⟩ ⟨h₂.1.le, h₂.2⟩ h).le
  have hR : Rfun P l₁ (hmax P) ≤ Rfun P l₂ (hmax P) := by
    rcases eq_or_lt_of_le hcon with h | h
    · rw [h]
    · exact (R_strictMono_lam P l₁ l₂ (hmax P) hγ hZL hZH h₁.1 h (hmax_pos P hθ hu)).le
  unfold Phi at hΦ₁ hΦ₂
  linarith

lemma C_lb_lt (P : Params) (C : ℝ → ℝ → ℝ) (c₁ c₂ : ℝ) (hθ : 0 < P.τθ) (hu : 0 < P.τu)
    (hγ : 0 < P.γ) (hβ1 : P.β < 1) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH)
    (l₁ l₂ : ℝ) (h₂ : 0 < l₂) (h12 : l₂ < l₁)
    (hΦ₁ : Phi P C c₁ l₁ = 0) (hΦ₂ : Phi P C c₂ l₂ = 0) : C c₁ l₁ < C c₂ l₂ := by
  have hR := R_strictMono_lam P l₂ l₁ (hmax P) hγ hZL hZH h₂ h12 (hmax_pos P hθ hu)
  unfold Phi at hΦ₁ hΦ₂
  have hE : Efun P C c₂ l₂ < Efun P C c₁ l₁ := by linarith
  unfold Efun at hE
  have := Real.exp_lt_exp.mp hE
  have h1β : 0 < 1 - P.β := by linarith
  have h2 : P.γ * C c₁ l₁ / (1 - P.β) < P.γ * C c₂ l₂ / (1 - P.β) := by linarith
  have h3 := (div_lt_div_iff_of_pos_right h1β).mp h2
  exact (mul_lt_mul_iff_of_pos_left hγ).mp h3

lemma ratio_bound (α lam a0 lb δ : ℝ) (hlb : 0 < lb) (hδ : 0 ≤ δ) (hl : lb / 2 ≤ lam)
    (hlam : |lam - lb| ≤ δ) (hα : |α - a0| ≤ δ) (ha0 : 0 ≤ a0) :
    |α / lam - a0 / lb| ≤ δ * (2 * (lb + a0) / lb ^ 2) := by
  have hlam0 : 0 < lam := by linarith
  have e : α / lam - a0 / lb = ((α - a0) * lb + a0 * (lb - lam)) / (lam * lb) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (mul_pos hlam0 hlb)]
  have h1 : |(α - a0) * lb + a0 * (lb - lam)| ≤ δ * (lb + a0) := by
    calc _ ≤ |(α - a0) * lb| + |a0 * (lb - lam)| := abs_add_le _ _
      _ = |α - a0| * lb + a0 * |lam - lb| := by
          rw [abs_mul, abs_mul, abs_of_pos hlb, abs_of_nonneg ha0, abs_sub_comm lb lam]
      _ ≤ δ * lb + a0 * δ := by
          have := mul_le_mul_of_nonneg_right hα hlb.le
          have := mul_le_mul_of_nonneg_left hlam ha0
          linarith
      _ = δ * (lb + a0) := by ring
  have h2 : lb / 2 * lb ≤ lam * lb := mul_le_mul_of_nonneg_right hl hlb.le
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ δ * (lb + a0) := h1
    _ = δ * (2 * (lb + a0) / lb ^ 2) * (lb / 2 * lb) := by field_simp
    _ ≤ δ * (2 * (lb + a0) / lb ^ 2) * (lam * lb) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

lemma log_lip (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : |Real.log (1 + a) - Real.log (1 + b)| ≤ |a - b| := by
  have k : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Real.log (1 + a) - Real.log (1 + b) ≤ |a - b| := by
    intro a b ha hb
    rw [← Real.log_div (by linarith) (by linarith)]
    refine le_trans (Real.log_le_sub_one_of_pos (by positivity)) ?_
    rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    have := le_abs_self (a - b)
    have : 0 ≤ |a - b| * b := mul_nonneg (abs_nonneg _) hb
    nlinarith
  rw [abs_le]; constructor
  · have := k b a hb ha; rw [abs_sub_comm] at this; linarith
  · exact k a b ha hb

lemma x0_le_aux (α lam γ S a0 lb : ℝ) (hγ : 0 < γ) (hS : 0 < S) (hlb : 0 < lb) (hα : 0 < α)
    (hαa : α ≤ a0 + 1) (hl : lb / 2 ≤ lam) :
    2 * α * γ / (lam * S) ≤ 2 * (a0 + 1) * γ / (lb / 2 * S) := by
  have hlam : 0 < lam := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have a1 : 2 * α * γ ≤ 2 * (a0 + 1) * γ := by nlinarith
  have a2 : lb / 2 * S ≤ lam * S := mul_le_mul_of_nonneg_right hl hS.le
  exact mul_le_mul a1 a2 (by positivity) (by nlinarith)

set_option maxHeartbeats 800000 in
lemma conv_x (P : Params) (hθ : 0 < P.τθ) (hu : 0 < P.τu) (hγ : 0 < P.γ) (hZL : 0 < P.ZL)
    (hZ : P.ZL < P.ZH) (lb a0 : ℝ) (hlb : 0 < lb) (ha0 : 0 < a0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη → ∀ x lam α : ℝ, 0 < x → 0 < α → Eq14 P τη x lam α →
      |lam - lb| < δ → |α - a0| < δ → |x - 2 * P.γ * a0 / (lb * (P.ZH + P.ZL))| < ε := by
  have hZH : 0 < P.ZH := by linarith
  have hS : 0 < P.ZH + P.ZL := by linarith
  have hΔ : 0 < P.ZH - P.ZL := by linarith
  set K1 := 2 * P.γ / (P.ZH + P.ZL) * (2 * (lb + a0) / lb ^ 2) with hK1
  have hK10 : 0 < K1 := by positivity
  set δ := min (min (lb / 2) 1) (ε / (2 * K1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδlb : δ ≤ lb / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδε : δ ≤ ε / (2 * K1) := min_le_right _ _
  set X0 := 2 * (a0 + 1) * P.γ / (lb / 2 * (P.ZH + P.ZL)) with hX0
  have hX00 : 0 < X0 := by positivity
  set B := 2 * X0 * (1 + P.τu * (a0 + 1) ^ 2) with hB
  have hB0 : 0 < B := by positivity
  set N := X0 * (B * P.ZH + P.τu * (a0 + 1) ^ 2) + B * (B * P.ZL * (P.ZH - P.ZL)) / (P.ZH + P.ZL) with hN
  have hN0 : 0 < N := by positivity
  clear_value N B X0 δ K1
  refine ⟨δ, hδ0, max (max 1 (2 * X0 * P.ZH)) (2 * N / ε + 1), ?_⟩
  intro τη hT x lam α hx hα h14 hl hαd
  have hT1 : 1 ≤ τη := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : 2 * X0 * P.ZH ≤ τη := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : 2 * N / ε + 1 ≤ τη := le_trans (le_max_right _ _) hT
  have hτ : 0 < τη := by linarith
  have hlam2 : lb / 2 ≤ lam := by
    have := (abs_lt.mp hl).1; linarith
  have hlam0 : 0 < lam := by linarith
  have hαa : α ≤ a0 + 1 := by have := (abs_lt.mp hαd).2; linarith
  obtain ⟨kup, klo⟩ := eq14_key P τη x lam α hτ hu hγ hZL hZ hx hlam0 hα h14
  have hx0 := x0_le_aux α lam P.γ (P.ZH + P.ZL) a0 lb hγ hS hlb hα hαa hlam2
  rw [← hX0] at hx0
  set x0 := 2 * α * P.γ / (lam * (P.ZH + P.ZL)) with hx0d
  have hx0p : 0 < x0 := by positivity
  have hQa : P.τu * α ^ 2 ≤ P.τu * (a0 + 1) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hα.le hαa 2) hu.le
  have hxB : x ≤ B := by
    rw [hB]
    exact x_bound_aux τη x x0 X0 P.ZH _ _ kup hx0 hx0p hQa (by positivity) hT1 hT2 hx hZH
  have hN' : |τη * (x - x0)| ≤ N := by
    rw [abs_le, hN]; constructor
    · have : x * (x * P.ZL * (P.ZH - P.ZL)) / (P.ZH + P.ZL) ≤ B * (B * P.ZL * (P.ZH - P.ZL)) / (P.ZH + P.ZL) := by
        apply div_le_div_of_nonneg_right _ hS.le
        have h1 : x * P.ZL * (P.ZH - P.ZL) ≤ B * P.ZL * (P.ZH - P.ZL) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxB hZL.le) hΔ.le
        exact mul_le_mul hxB h1 (by positivity) hB0.le
      have : 0 ≤ X0 * (B * P.ZH + P.τu * (a0 + 1) ^ 2) := by positivity
      linarith
    · have : x0 * (x * P.ZH + P.τu * α ^ 2) ≤ X0 * (B * P.ZH + P.τu * (a0 + 1) ^ 2) := by
        apply mul_le_mul hx0 _ (by positivity) hX00.le
        have := mul_le_mul_of_nonneg_right hxB hZH.le
        linarith
      have : 0 ≤ B * (B * P.ZL * (P.ZH - P.ZL)) / (P.ZH + P.ZL) := by positivity
      linarith
  have h1 : |x - x0| < ε / 2 := by
    rw [abs_mul, abs_of_pos hτ] at hN'
    have : N / τη < ε / 2 := by
      rw [div_lt_iff₀ hτ]
      have : 2 * N / ε < τη := by linarith
      rw [div_lt_iff₀ hε] at this; linarith
    have : |x - x0| ≤ N / τη := by rw [le_div_iff₀ hτ, mul_comm]; exact hN'
    linarith
  have h2 : |x0 - 2 * P.γ * a0 / (lb * (P.ZH + P.ZL))| ≤ ε / 2 := by
    have e : x0 - 2 * P.γ * a0 / (lb * (P.ZH + P.ZL)) = 2 * P.γ / (P.ZH + P.ZL) * (α / lam - a0 / lb) := by
      rw [hx0d]; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have := ratio_bound α lam a0 lb δ hlb hδ0.le hlam2 (abs_lt.mp hl |> fun h => abs_le.mpr ⟨h.1.le, h.2.le⟩)
      (abs_le.mpr ⟨(abs_lt.mp hαd).1.le, (abs_lt.mp hαd).2.le⟩) ha0.le
    have h3 := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 2 * P.γ / (P.ZH + P.ZL))
    have h4 : 2 * P.γ / (P.ZH + P.ZL) * (δ * (2 * (lb + a0) / lb ^ 2)) = δ * K1 := by rw [hK1]; ring
    have h5 : δ * K1 ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_right hδε hK10.le
      have e2 : ε / (2 * K1) * K1 = ε / 2 := by field_simp
      linarith
    linarith
  calc |x - 2 * P.γ * a0 / (lb * (P.ZH + P.ZL))|
      = |(x - x0) + (x0 - 2 * P.γ * a0 / (lb * (P.ZH + P.ZL)))| := by ring_nf
    _ ≤ |x - x0| + |x0 - 2 * P.γ * a0 / (lb * (P.ZH + P.ZL))| := abs_add_le _ _
    _ < ε := by linarith

lemma ratio_eq_H (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hx : 0 < x) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH) (hα : 0 < α) (hγ : 0 < P.γ) :
    varU P τη α / varH P τη x α = 1 + qfun P P.ZH (lamOf P τη x α) (hfun P α) * rhoH P τη x α := by
  have h := y_eq_gen P τη x α P.ZH P.ZL hθ hτ hu hx hZH hZL hα hγ (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩)
  simp only [varU, varH]
  rw [← sub_eq_iff_eq_add', h]
  unfold qfun hfun rhoH
  ring_nf

lemma ratio_eq_L (P : Params) (τη x α : ℝ) (hθ : 0 < P.τθ) (hτ : 0 < τη) (hu : 0 < P.τu)
    (hx : 0 < x) (hZL : 0 < P.ZL) (hZH : 0 < P.ZH) (hα : 0 < α) (hγ : 0 < P.γ) :
    varU P τη α / varL P τη x α = 1 + qfun P P.ZL (lamOf P τη x α) (hfun P α) * rhoL P τη x α := by
  have h := y_eq_gen P τη x α P.ZL P.ZH hθ hτ hu hx hZL hZH hα hγ (Or.inr rfl) (Or.inr ⟨rfl, rfl⟩)
  simp only [varU, varL]
  rw [← sub_eq_iff_eq_add', h]
  unfold qfun hfun rhoL
  ring_nf

noncomputable def perfLim (P : Params) (lb : ℝ) : ℝ :=
  1 / 2 * (1 / (2 * P.γ) * Real.log (1 + qfun P P.ZH lb (hmax P))
    + 1 / (2 * P.γ) * Real.log (1 + qfun P P.ZL lb (hmax P)))

lemma perfLim_anti (P : Params) (hθ : 0 < P.τθ) (hu : 0 < P.τu) (hγ : 0 < P.γ)
    (hZL : 0 < P.ZL) (hZH : 0 < P.ZH) (l₁ l₂ : ℝ) (h₂ : 0 < l₂) (h12 : l₂ < l₁) :
    perfLim P l₁ < perfLim P l₂ := by
  have hS : 0 < P.ZH + P.ZL := by linarith
  have hm := hmax_pos P hθ hu
  have k : ∀ Z, 0 < Z → Real.log (1 + qfun P Z l₁ (hmax P)) < Real.log (1 + qfun P Z l₂ (hmax P)) := by
    intro Z hZ
    have h1 : 0 ≤ qfun P Z l₁ (hmax P) := qfun_nonneg P Z l₁ _ hγ hZ hS (by linarith) hm.le
    apply Real.log_lt_log (by linarith)
    have : qfun P Z l₁ (hmax P) < qfun P Z l₂ (hmax P) := by
      unfold qfun; exact div_lt_div_of_pos_left (by positivity) h₂ h12
    linarith
  have a := k P.ZH hZH
  have b := k P.ZL hZL
  unfold perfLim
  have hg : 0 < 1 / (2 * P.γ) := by positivity
  have a' := mul_lt_mul_of_pos_left a hg
  have b' := mul_lt_mul_of_pos_left b hg
  linarith

set_option maxHeartbeats 1600000 in
lemma conv_perf (P : Params) (hθ : 0 < P.τθ) (hu : 0 < P.τu) (hγ : 0 < P.γ) (hZL : 0 < P.ZL)
    (hZ : P.ZL < P.ZH) (lb XB : ℝ) (hlb : 0 < lb) (hXB : 0 < XB) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη → ∀ x lam α : ℝ, 0 < x → 0 < α → Eq14 P τη x lam α →
      x ≤ XB → |lam - lb| < δ → |α - Real.sqrt (P.τθ / P.τu)| < δ →
        |performance P τη x α - perfLim P lb| < ε := by
  have hZH : 0 < P.ZH := by linarith
  have hS : 0 < P.ZH + P.ZL := by linarith
  have hΔ : 0 < P.ZH - P.ZL := by linarith
  have hm := hmax_pos P hθ hu
  have hst : 0 < Real.sqrt P.τθ := Real.sqrt_pos.mpr hθ
  have hsu : 0 < Real.sqrt P.τu := Real.sqrt_pos.mpr hu
  set κH := 2 * P.γ * P.ZH / (P.ZH + P.ZL) with hκH
  have hκH0 : 0 < κH := by positivity
  set c2 := P.τu / (2 * Real.sqrt P.τθ * Real.sqrt P.τu * P.τθ) with hc2
  have hc20 : 0 < c2 := by positivity
  set K3 := (1 + c2) * (2 * (lb + hmax P) / lb ^ 2) with hK3
  have hK30 : 0 < K3 := by positivity
  set Qm := κH * hmax P / (lb / 2) with hQm
  have hQm0 : 0 < Qm := by positivity
  set D1 := XB * P.ZH * (P.ZH - P.ZL) / (P.ZH + P.ZL) with hD1
  have hD10 : 0 < D1 := by positivity
  set E1 := P.τθ * (1 + D1) + D1 with hE1
  have hE10 : 0 < E1 := by positivity
  -- |perf - lim| ≤ (1/(4γ)) * 2 * (Qm*E1/τη + κH*δ*K3)
  set δ := min (min (lb / 2) 1) (ε * P.γ / (κH * K3 + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδlb : δ ≤ lb / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδε : δ ≤ ε * P.γ / (κH * K3 + 1) := min_le_right _ _
  clear_value δ E1 D1 Qm K3 c2 κH
  refine ⟨δ, hδ0, max 1 (Qm * E1 / (ε * P.γ) + 1), ?_⟩
  intro τη hT x lam α hx hα h14 hxB hl hαd
  have hT1 : 1 ≤ τη := le_trans (le_max_left _ _) hT
  have hT2 : Qm * E1 / (ε * P.γ) + 1 ≤ τη := le_trans (le_max_right _ _) hT
  have hτ : 0 < τη := by linarith
  have hlam2 : lb / 2 ≤ lam := by have := (abs_lt.mp hl).1; linarith
  have hlam0 : 0 < lam := by linarith
  have hxH := mul_pos hx hZH
  have hxL := mul_pos hx hZL
  have hlamq := (eq14_iff P τη x lam α hτ hu hxH hxL).mp h14
  -- rho errors
  have hDb : x * P.ZH * (P.ZH - P.ZL) / (τη * (P.ZH + P.ZL)) ≤ D1 / τη := by
    rw [hD1, div_div, mul_comm (P.ZH + P.ZL) τη]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxB hZH.le) hΔ.le
  obtain ⟨eH, eL⟩ := rho_err P τη x α (D1 / τη) hθ hτ hu hx hZL hZ hDb
  have hρe : P.τθ / (P.τθ + τη) * (1 + D1 / τη) + D1 / τη ≤ E1 / τη := by
    have a1 : P.τθ / (P.τθ + τη) ≤ P.τθ / τη := div_le_div_of_nonneg_left hθ.le hτ (by linarith)
    have a2 : D1 / τη ≤ D1 := div_le_self hD10.le hT1
    have a3 : P.τθ / (P.τθ + τη) * (1 + D1 / τη) ≤ P.τθ / τη * (1 + D1) :=
      mul_le_mul a1 (by linarith) (by positivity) (by positivity)
    have : P.τθ / τη * (1 + D1) + D1 / τη = E1 / τη := by rw [hE1]; field_simp
    linarith
  -- h error
  have hh0 := hfun_nonneg P α hθ hu hα.le
  have hhle := hfun_le P α hθ hu
  have hhd : |hfun P α - hmax P| ≤ δ * (1 + c2) := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hhle), hmax_sub P α hθ hu]
    have hsq : (α - Real.sqrt (P.τθ / P.τu)) ^ 2 ≤ δ := by
      have : |α - Real.sqrt (P.τθ / P.τu)| ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hαd.le 2
      rw [sq_abs] at this
      exact le_trans this (pow_le_of_le_one hδ0.le hδ1 two_ne_zero)
    have hden : 2 * Real.sqrt P.τθ * Real.sqrt P.τu * P.τθ ≤
        2 * Real.sqrt P.τθ * Real.sqrt P.τu * (P.τθ + α ^ 2 * P.τu) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
    calc P.τu * (α - Real.sqrt (P.τθ / P.τu)) ^ 2 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu * (P.τθ + α ^ 2 * P.τu))
        ≤ P.τu * (α - Real.sqrt (P.τθ / P.τu)) ^ 2 / (2 * Real.sqrt P.τθ * Real.sqrt P.τu * P.τθ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = c2 * (α - Real.sqrt (P.τθ / P.τu)) ^ 2 := by rw [hc2]; ring
      _ ≤ c2 * δ := mul_le_mul_of_nonneg_left hsq hc20.le
      _ ≤ δ * (1 + c2) := by
          have : δ * (1 + c2) = c2 * δ + δ := by ring
          linarith
  have hrb := ratio_bound (hfun P α) lam (hmax P) lb (δ * (1 + c2)) hlb (by positivity) hlam2
    (le_trans (abs_le.mpr ⟨(abs_lt.mp hl).1.le, (abs_lt.mp hl).2.le⟩)
      (le_mul_of_one_le_right hδ0.le (by linarith))) hhd hm.le
  have hrb' : |hfun P α / lam - hmax P / lb| ≤ δ * K3 := by
    rw [hK3]; linarith [hrb, show δ * (1 + c2) * (2 * (lb + hmax P) / lb ^ 2) = δ * ((1 + c2) * (2 * (lb + hmax P) / lb ^ 2)) by ring]
  -- per-skill estimate
  have key : ∀ Z ρ, 0 < Z → Z ≤ P.ZH → 0 ≤ ρ → |ρ - 1| ≤ E1 / τη →
      |Real.log (1 + qfun P Z lam (hfun P α) * ρ) - Real.log (1 + qfun P Z lb (hmax P))| ≤
        Qm * (E1 / τη) + κH * (δ * K3) := by
    intro Z ρ hZ0 hZle hρ0 hρ
    have hq0 := qfun_nonneg P Z lam (hfun P α) hγ hZ0 hS hlam0 hh0
    have hqb : qfun P Z lam (hfun P α) ≤ Qm := by
      rw [hQm]; unfold qfun
      refine le_trans ?_ (q_bound_aux _ _ _ _ _ hκH0.le hhle hh0 (by linarith) hlam2)
      apply div_le_div_of_nonneg_right _ hlam0.le
      apply mul_le_mul_of_nonneg_right _ hh0
      rw [hκH]; apply div_le_div_of_nonneg_right _ hS.le
      exact mul_le_mul_of_nonneg_left hZle (by positivity)
    refine le_trans (log_lip _ _ (mul_nonneg hq0 hρ0) (qfun_nonneg P Z lb _ hγ hZ0 hS hlb hm.le)) ?_
    have e : qfun P Z lam (hfun P α) * ρ - qfun P Z lb (hmax P) =
        qfun P Z lam (hfun P α) * (ρ - 1) + 2 * P.γ * Z / (P.ZH + P.ZL) * (hfun P α / lam - hmax P / lb) := by
      unfold qfun; ring
    rw [e]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_pos (by positivity : 0 < 2 * P.γ * Z / (P.ZH + P.ZL))]
    have k1 := mul_le_mul hqb hρ (abs_nonneg _) hQm0.le
    have hκZ : 2 * P.γ * Z / (P.ZH + P.ZL) ≤ κH := by
      rw [hκH]; apply div_le_div_of_nonneg_right _ hS.le
      exact mul_le_mul_of_nonneg_left hZle (by positivity)
    have k2 := mul_le_mul hκZ hrb' (abs_nonneg _) hκH0.le
    linarith
  have kH := key P.ZH (rhoH P τη x α) hZH le_rfl (rhoH_pos P τη x α hθ hτ hu hx hZL hZH).le (le_trans eH hρe)
  have kL := key P.ZL (rhoL P τη x α) hZL hZ.le (rhoL_pos P τη x α hθ hτ hu hx hZL hZH).le (le_trans eL hρe)
  have pe : performance P τη x α = 1 / 2 * (1 / (2 * P.γ) * Real.log (1 + qfun P P.ZH lam (hfun P α) * rhoH P τη x α)
      + 1 / (2 * P.γ) * Real.log (1 + qfun P P.ZL lam (hfun P α) * rhoL P τη x α)) := by
    unfold performance
    rw [ratio_eq_H P τη x α hθ hτ hu hx hZL hZH hα hγ, ratio_eq_L P τη x α hθ hτ hu hx hZL hZH hα hγ, ← hlamq]
  rw [pe]
  unfold perfLim
  set aH := Real.log (1 + qfun P P.ZH lam (hfun P α) * rhoH P τη x α) - Real.log (1 + qfun P P.ZH lb (hmax P))
  set aL := Real.log (1 + qfun P P.ZL lam (hfun P α) * rhoL P τη x α) - Real.log (1 + qfun P P.ZL lb (hmax P))
  have e : 1 / 2 * (1 / (2 * P.γ) * Real.log (1 + qfun P P.ZH lam (hfun P α) * rhoH P τη x α)
      + 1 / (2 * P.γ) * Real.log (1 + qfun P P.ZL lam (hfun P α) * rhoL P τη x α)) -
      1 / 2 * (1 / (2 * P.γ) * Real.log (1 + qfun P P.ZH lb (hmax P))
        + 1 / (2 * P.γ) * Real.log (1 + qfun P P.ZL lb (hmax P))) = (aH + aL) / (4 * P.γ) := by
    simp only [aH, aL]; field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * P.γ), div_lt_iff₀ (by positivity)]
  have hsum : |aH + aL| ≤ 2 * (Qm * (E1 / τη) + κH * (δ * K3)) := by
    have := abs_add_le aH aL; linarith
  -- 2*(Qm E1/τη + κH δ K3) < ε * (4γ)
  have t1 : Qm * (E1 / τη) < ε * P.γ := by
    rw [mul_div_assoc', div_lt_iff₀ hτ]
    have : Qm * E1 / (ε * P.γ) < τη := by linarith
    rw [div_lt_iff₀ (by positivity)] at this; linarith
  have t2 : κH * (δ * K3) < ε * P.γ := by
    have h1 : δ * (κH * K3 + 1) ≤ ε * P.γ := by
      have := mul_le_mul_of_nonneg_right hδε (by positivity : (0:ℝ) ≤ κH * K3 + 1)
      have e2 : ε * P.γ / (κH * K3 + 1) * (κH * K3 + 1) = ε * P.γ := by field_simp
      linarith
    have : κH * (δ * K3) = δ * (κH * K3 + 1) - δ := by ring
    linarith
  linarith

/-- one cost level: all first-order convergences at once -/
lemma conv_all (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (hC : IsCostFamily C) (c : ℝ)
    (hc : 0 < c) (lb : ℝ) (hlb : lb ∈ Set.Ioo (0:ℝ) 1) (hΦ : Phi P C c lb = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη → ∀ (X : Clarity) (lam α : ℝ), IsEquilibrium P C c τη X lam α →
      ∃ x, X = .finite x ∧ |lam - lb| < ε ∧
        |x - 2 * P.γ * Real.sqrt (P.τθ / P.τu) / (lb * (P.ZH + P.ZL))| < ε ∧
        |C c lam - C c lb| < ε ∧ |performance P τη x α - perfLim P lb| < ε := by
  have hP' := hP
  obtain ⟨hθ, hu, hγ, hβ0, hβ1, hZL, hZ⟩ := hP
  obtain ⟨hCc, hCm, hC0, hCt⟩ := hC.1 c hc
  have ha0 : 0 < Real.sqrt (P.τθ / P.τu) := Real.sqrt_pos.mpr (by positivity)
  have hS : 0 < P.ZH + P.ZL := by linarith
  obtain ⟨δC, hδC, hδC'⟩ := Metric.continuousWithinAt_iff.mp (hCc lb ⟨hlb.1.le, hlb.2⟩) ε hε
  obtain ⟨δx, hδx, Tx, hTx⟩ := conv_x P hθ hu hγ hZL hZ lb _ hlb.1 ha0 (min ε 1) (by positivity)
  set Xb := 2 * P.γ * Real.sqrt (P.τθ / P.τu) / (lb * (P.ZH + P.ZL)) with hXb
  have hXb0 : 0 < Xb := by have := hlb.1; positivity
  obtain ⟨δp, hδp, Tp, hTp⟩ := conv_perf P hθ hu hγ hZL hZ lb (Xb + 1) hlb.1 (by linarith) ε hε
  set δ := min (min ε δC) (min δx δp) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨Ta, hTa⟩ := main_asym P hP' C hC c hc lb hlb hΦ δ hδ0
  refine ⟨max Ta (max Tx Tp), ?_⟩
  intro τη hT X lam α hE
  have hTa' : Ta ≤ τη := le_trans (le_max_left _ _) hT
  have hTx' : Tx ≤ τη := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTp' : Tp ≤ τη := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  obtain ⟨⟨x, rfl⟩, hl, hα⟩ := hTa τη hTa' _ lam α hE
  obtain ⟨⟨hx, hl0, hl1, hα0, h14, h19⟩, -⟩ := hE
  have hδε : δ ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδC2 : δ ≤ δC := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδx2 : δ ≤ δx := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδp2 : δ ≤ δp := le_trans (min_le_right _ _) (min_le_right _ _)
  have hxc := hTx τη hTx' x lam α hx hα0 h14 (lt_of_lt_of_le hl hδx2) (lt_of_lt_of_le hα hδx2)
  have hxB : x ≤ Xb + 1 := by
    have := (abs_lt.mp hxc).2; have := min_le_right ε 1; linarith
  refine ⟨x, rfl, lt_of_lt_of_le hl hδε, lt_of_lt_of_le hxc (min_le_left _ _), ?_, ?_⟩
  · have := hδC' ⟨hl0.le, hl1⟩ (by rw [Real.dist_eq]; exact lt_of_lt_of_le hl hδC2)
    rwa [Real.dist_eq] at this
  · exact hTp τη hTp' x lam α hx hα0 h14 hxB (lt_of_lt_of_le hl hδp2) (lt_of_lt_of_le hα hδp2)

theorem goal_first_order (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (hC : IsCostFamily C)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) :
    ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη →
      ∀ (X₁ : Clarity) (lam₁ α₁ : ℝ) (X₂ : Clarity) (lam₂ α₂ : ℝ),
        IsEquilibrium P C c₁ τη X₁ lam₁ α₁ → IsEquilibrium P C c₂ τη X₂ lam₂ α₂ →
        ∃ x₁ x₂ : ℝ, X₁ = .finite x₁ ∧ X₂ = .finite x₂ ∧
          lam₂ < lam₁ ∧ x₁ < x₂ ∧
          dataPrice P τη x₁ α₁ < dataPrice P τη x₂ α₂ ∧
          performance P τη x₁ α₁ < performance P τη x₂ α₂ := by
  have hP' := hP
  obtain ⟨hθ, hu, hγ, hβ0, hβ1, hZL, hZ⟩ := hP
  have hc₂ : 0 < c₂ := by linarith
  have hZH : 0 < P.ZH := by linarith
  have hS : 0 < P.ZH + P.ZL := by linarith
  have h1β : 0 < 1 - P.β := by linarith
  obtain ⟨hCc₁, hCm₁, hC0₁, hCt₁⟩ := hC.1 c₁ hc₁
  obtain ⟨hCc₂, hCm₂, hC0₂, hCt₂⟩ := hC.1 c₂ hc₂
  obtain ⟨l₁, hl₁, hΦ₁⟩ := Phi_root P C c₁ hθ hu hγ hβ1 hZL hZ hCc₁ hCm₁ hC0₁ hCt₁
  obtain ⟨l₂, hl₂, hΦ₂⟩ := Phi_root P C c₂ hθ hu hγ hβ1 hZL hZ hCc₂ hCm₂ hC0₂ hCt₂
  have h21 := lb_anti P C hC c₁ c₂ hc₁ hc hθ hu hγ hβ1 hZL hZH l₁ l₂ hl₁ hl₂ hΦ₁ hΦ₂
  have ha0 : 0 < Real.sqrt (P.τθ / P.τu) := Real.sqrt_pos.mpr (by positivity)
  set X1 := 2 * P.γ * Real.sqrt (P.τθ / P.τu) / (l₁ * (P.ZH + P.ZL)) with hX1
  set X2 := 2 * P.γ * Real.sqrt (P.τθ / P.τu) / (l₂ * (P.ZH + P.ZL)) with hX2
  have hX12 : X1 < X2 := by
    rw [hX1, hX2]
    apply div_lt_div_of_pos_left (by positivity) (by have := hl₂.1; positivity)
    exact mul_lt_mul_of_pos_right h21 hS
  have hC12 := C_lb_lt P C c₁ c₂ hθ hu hγ hβ1 hZL hZH l₁ l₂ hl₂.1 h21 hΦ₁ hΦ₂
  have hP12 := perfLim_anti P hθ hu hγ hZL hZH l₁ l₂ hl₂.1 h21
  set g := min (min (l₁ - l₂) (X2 - X1)) (min (C c₂ l₂ - C c₁ l₁) (perfLim P l₂ - perfLim P l₁)) / 2 with hg
  have hg0 : 0 < g := by
    have : 0 < min (min (l₁ - l₂) (X2 - X1)) (min (C c₂ l₂ - C c₁ l₁) (perfLim P l₂ - perfLim P l₁)) := by
      apply lt_min <;> apply lt_min <;> linarith
    positivity
  have g1 : 2 * g ≤ l₁ - l₂ := by
    have := min_le_left (min (l₁ - l₂) (X2 - X1)) (min (C c₂ l₂ - C c₁ l₁) (perfLim P l₂ - perfLim P l₁))
    have := min_le_left (l₁ - l₂) (X2 - X1); rw [hg]; linarith
  have g2 : 2 * g ≤ X2 - X1 := by
    have := min_le_left (min (l₁ - l₂) (X2 - X1)) (min (C c₂ l₂ - C c₁ l₁) (perfLim P l₂ - perfLim P l₁))
    have := min_le_right (l₁ - l₂) (X2 - X1); rw [hg]; linarith
  have g3 : 2 * g ≤ C c₂ l₂ - C c₁ l₁ := by
    have := min_le_right (min (l₁ - l₂) (X2 - X1)) (min (C c₂ l₂ - C c₁ l₁) (perfLim P l₂ - perfLim P l₁))
    have := min_le_left (C c₂ l₂ - C c₁ l₁) (perfLim P l₂ - perfLim P l₁); rw [hg]; linarith
  have g4 : 2 * g ≤ perfLim P l₂ - perfLim P l₁ := by
    have := min_le_right (min (l₁ - l₂) (X2 - X1)) (min (C c₂ l₂ - C c₁ l₁) (perfLim P l₂ - perfLim P l₁))
    have := min_le_right (C c₂ l₂ - C c₁ l₁) (perfLim P l₂ - perfLim P l₁); rw [hg]; linarith
  clear_value g X1 X2
  obtain ⟨T₁, hT₁⟩ := conv_all P hP' C hC c₁ hc₁ l₁ hl₁ hΦ₁ g hg0
  obtain ⟨T₂, hT₂⟩ := conv_all P hP' C hC c₂ hc₂ l₂ hl₂ hΦ₂ g hg0
  refine ⟨max T₁ T₂, ?_⟩
  intro τη hT X₁ lam₁ α₁ X₂ lam₂ α₂ hE₁ hE₂
  obtain ⟨x₁, rfl, a1, b1, c1, d1⟩ := hT₁ τη (le_trans (le_max_left _ _) hT) X₁ lam₁ α₁ hE₁
  obtain ⟨x₂, rfl, a2, b2, c2, d2⟩ := hT₂ τη (le_trans (le_max_right _ _) hT) X₂ lam₂ α₂ hE₂
  rw [← hX1] at b1; rw [← hX2] at b2
  have h19₁ := hE₁.1.2.2.2.2.2
  have h19₂ := hE₂.1.2.2.2.2.2
  refine ⟨x₁, x₂, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · have := (abs_lt.mp a1).1; have := (abs_lt.mp a2).2; linarith
  · have := (abs_lt.mp b1).2; have := (abs_lt.mp b2).1; linarith
  · unfold dataPrice
    have e1 : gain P τη x₁ α₁ = C c₁ lam₁ / (1 - P.β) := by
      rw [eq_div_iff h1β.ne']; linarith
    have e2 : gain P τη x₂ α₂ = C c₂ lam₂ / (1 - P.β) := by
      rw [eq_div_iff h1β.ne']; linarith
    rw [e1, e2]
    apply mul_lt_mul_of_pos_left _ hβ0
    apply div_lt_div_of_pos_right _ h1β
    have := (abs_lt.mp c1).2; have := (abs_lt.mp c2).1; linarith
  · have := (abs_lt.mp d1).2; have := (abs_lt.mp d2).1; linarith

end GRAsym

open GRAsym

theorem solution (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (hC : IsCostFamily C)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) :
    ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη →
      ∀ (X₁ : Clarity) (lam₁ α₁ : ℝ) (X₂ : Clarity) (lam₂ α₂ : ℝ),
        IsEquilibrium P C c₁ τη X₁ lam₁ α₁ → IsEquilibrium P C c₂ τη X₂ lam₂ α₂ →
        ∃ x₁ x₂ : ℝ, X₁ = .finite x₁ ∧ X₂ = .finite x₂ ∧
          lam₂ < lam₁ ∧ x₁ < x₂ ∧
          dataPrice P τη x₁ α₁ < dataPrice P τη x₂ α₂ ∧
          priceInformativeness P τη α₁ < priceInformativeness P τη α₂ ∧
          costOfCapital P τη x₂ lam₂ α₂ < costOfCapital P τη x₁ lam₁ α₁ ∧
          returnVolatility P τη x₂ lam₂ α₂ < returnVolatility P τη x₁ lam₁ α₁ ∧
          performance P τη x₁ α₁ < performance P τη x₂ α₂ := by
  obtain ⟨TA, hTA⟩ := goal_first_order P hP C hC c₁ c₂ hc₁ hc
  obtain ⟨TB, hTB⟩ := SkillData.GoldRush.proposition_5_market_quality P hP C hC c₁ c₂ hc₁ hc
  refine ⟨max TA TB, ?_⟩
  intro τη hT X₁ lam₁ α₁ X₂ lam₂ α₂ hE₁ hE₂
  obtain ⟨x₁, x₂, h1, h2, a, b, d, p⟩ := hTA τη (le_trans (le_max_left _ _) hT) X₁ lam₁ α₁ X₂ lam₂ α₂ hE₁ hE₂
  obtain ⟨q1, q2, q3⟩ := hTB τη (le_trans (le_max_right _ _) hT) X₁ lam₁ α₁ X₂ lam₂ α₂ hE₁ hE₂ x₁ x₂ h1 h2
  exact ⟨x₁, x₂, h1, h2, a, b, d, q1, q2, q3, p⟩
