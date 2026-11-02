-- Prove2me | solution 1 for TechSourcing.PTS.monotone_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T03:31:19.12771+00:00
-- url     : https://prove2.me/submissions/6cd8cd83-60fc-41b5-9318-94c92e099bf3

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

open TechSourcing.PTS

private lemma s_lt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (9 * a ^ 2 + 10 * a * b + b ^ 2) < 3 * a + 5 * b / 3 := by
  rw [Real.sqrt_lt' (by positivity)]
  nlinarith [sq_nonneg b, mul_pos hb hb]

private lemma g_anti (b : ℝ) (hb : 0 < b) :
    StrictAntiOn (fun a : ℝ => 3 * (a + b) - Real.sqrt (9 * a ^ 2 + 10 * a * b + b ^ 2))
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  simp only
  set s1 := Real.sqrt (9 * x ^ 2 + 10 * x * b + b ^ 2)
  set s2 := Real.sqrt (9 * y ^ 2 + 10 * y * b + b ^ 2)
  have h1 : s1 ^ 2 = 9 * x ^ 2 + 10 * x * b + b ^ 2 := Real.sq_sqrt (by positivity)
  have h2 : s2 ^ 2 = 9 * y ^ 2 + 10 * y * b + b ^ 2 := Real.sq_sqrt (by positivity)
  have l1 := s_lt x b hx hb
  have l2 := s_lt y b hy hb
  have p1 : 0 ≤ s1 := Real.sqrt_nonneg _
  have p2 : 0 ≤ s2 := Real.sqrt_nonneg _
  -- (s2 - s1)(s1 + s2) = (y - x)(9(x+y) + 10 b) > 3 (y - x)(s1 + s2)
  have key : (s2 - s1) * (s1 + s2) = (y - x) * (9 * (x + y) + 10 * b) := by nlinarith
  have hpos : 0 < s1 + s2 := by
    have : 0 < s2 := Real.sqrt_pos.2 (by positivity)
    linarith
  have : 3 * (y - x) * (s1 + s2) < (s2 - s1) * (s1 + s2) := by
    rw [key]; nlinarith
  have : 3 * (y - x) < s2 - s1 := lt_of_mul_lt_mul_right this hpos.le
  linarith

theorem solution (P : Params) (hP : P.Standing) :
    StrictAntiOn (fun a : ℝ => gammaHat { P with a := a }) (Set.Ioi 0) ∧
      StrictMonoOn (fun a : ℝ => Fcmp { P with a := a }) (Set.Ioi 0) ∧
      ∃ q₂ q₁ q₀ : ℝ, 0 < q₂ ∧
        ∀ β : ℝ, Fcmp { P with β := β } = q₂ * β ^ 2 + q₁ * β + q₀ := by
  obtain ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩ := hP
  have hγ : StrictAntiOn (fun a : ℝ => gammaHat { P with a := a }) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have := g_anti P.b hb hx hy hxy
    simp only [gammaHat, TechSourcing.PTS.sq] at this ⊢
    exact div_lt_div_of_pos_right this (by positivity)
  refine ⟨hγ, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_Ioi] at hx hy
    have hgx := hγ hx hy hxy
    simp only at hgx
    simp only [Fcmp, Wb, Lb]
    set gx := gammaHat { P with a := x }
    set gy := gammaHat { P with a := y }
    have hL : 0 ≤ P.D ^ 2 * (1 - P.β) * P.β / (2 * P.c) := by
      have : 0 ≤ 1 - P.β := by linarith
      positivity
    have h1 : gy * (P.D ^ 2 * (1 - P.β) * P.β / (2 * P.c)) ≤
        gx * (P.D ^ 2 * (1 - P.β) * P.β / (2 * P.c)) :=
      mul_le_mul_of_nonneg_right hgx.le hL
    have h2 : Real.sqrt (9 / P.b ^ 2 + 10 / (y * P.b) + 1 / y ^ 2) ≤
        Real.sqrt (9 / P.b ^ 2 + 10 / (x * P.b) + 1 / x ^ 2) := by
      apply Real.sqrt_le_sqrt
      have : 10 / (y * P.b) ≤ 10 / (x * P.b) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_right hxy.le hb.le)
      have : 1 / y ^ 2 ≤ 1 / x ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
      linarith
    have h3 : 2 / (3 * y) < 2 / (3 * x) :=
      div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)
    nlinarith
  · set k := 1 / 3 + 2 / 3 * gammaHat P
    have hk : 0 < k := by
      have := s_lt P.a P.b ha hb
      have : 0 < gammaHat P := by
        unfold gammaHat TechSourcing.PTS.sq
        apply div_pos _ (by positivity)
        linarith
      simp only [k]; linarith
    set C := 2 / 3 * Real.sqrt (9 / P.b ^ 2 + 10 / (P.a * P.b) + 1 / P.a ^ 2)
      + 2 / (3 * P.a) + 2 / (3 * P.b)
    refine ⟨k * P.D ^ 2 / (2 * P.c), (1 - P.R) * P.D - k * P.D ^ 2 / (2 * P.c),
      P.R * P.D - C, by positivity, fun β => ?_⟩
    have hg : gammaHat { P with β := β } = gammaHat P := rfl
    simp only [Fcmp, Wb, Lb, hg]
    simp only [C, k]
    field_simp
    ring
