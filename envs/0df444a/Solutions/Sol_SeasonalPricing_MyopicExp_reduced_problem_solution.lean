-- Prove2me | solution 1 for SeasonalPricing.MyopicExp.reduced_problem_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T14:08:31.336599+00:00
-- url     : https://prove2.me/submissions/97733def-06a0-444d-bb2c-91ab38e72c01

import Mathlib

lemma a22a8542_le_exp_sub_one (u : ℝ) : u ≤ Real.exp (u - 1) := by
  linarith [Real.add_one_le_exp (u - 1)]

lemma a22a8542_lt_exp_sub_one (u : ℝ) (h : u ≠ 1) : u < Real.exp (u - 1) := by
  have := Real.add_one_lt_exp (sub_ne_zero.mpr h)
  linarith

lemma a22a8542_exp_id (p1 p2 : ℝ) :
    Real.exp (p1 - p2 - 1) * Real.exp (-p1) = Real.exp (-p2 - 1) := by
  rw [← Real.exp_add]; ring_nf

lemma a22a8542_A (p1 p2 : ℝ) : (p1 - p2) * Real.exp (-p1) ≤ Real.exp (-p2 - 1) := by
  rw [← a22a8542_exp_id p1 p2]
  exact mul_le_mul_of_nonneg_right (a22a8542_le_exp_sub_one _) (Real.exp_pos _).le

lemma a22a8542_A_lt (p1 p2 : ℝ) (h : p1 - p2 ≠ 1) :
    (p1 - p2) * Real.exp (-p1) < Real.exp (-p2 - 1) := by
  rw [← a22a8542_exp_id p1 p2]
  exact mul_lt_mul_of_pos_right (a22a8542_lt_exp_sub_one _ h) (Real.exp_pos _)

lemma a22a8542_exp_id2 (p2 c : ℝ) :
    Real.exp (-p2) * Real.exp (p2 + c - 1) = Real.exp (-1 + c) := by
  rw [← Real.exp_add]; ring_nf

lemma a22a8542_B (p2 c : ℝ) : Real.exp (-p2) * (p2 + c) ≤ Real.exp (-1 + c) := by
  rw [← a22a8542_exp_id2 p2 c]
  exact mul_le_mul_of_nonneg_left (a22a8542_le_exp_sub_one _) (Real.exp_pos _).le

lemma a22a8542_B_lt (p2 c : ℝ) (h : p2 ≠ 1 - c) :
    Real.exp (-p2) * (p2 + c) < Real.exp (-1 + c) := by
  rw [← a22a8542_exp_id2 p2 c]
  refine mul_lt_mul_of_pos_left (a22a8542_lt_exp_sub_one _ ?_) (Real.exp_pos _)
  intro h'; apply h; linarith

lemma a22a8542_mid (p2 T : ℝ) :
    p2 * Real.exp (-p2) + T * Real.exp (-p2 - 1) = Real.exp (-p2) * (p2 + T / Real.exp 1) := by
  rw [Real.exp_sub]
  have := Real.exp_pos 1
  field_simp

lemma a22a8542_f (lam T p1 p2 : ℝ) :
    p2 * lam * Real.exp (-p2) + (p1 - p2) * lam * T * Real.exp (-p1)
      = lam * (p2 * Real.exp (-p2) + T * ((p1 - p2) * Real.exp (-p1))) := by ring

theorem solution (lam T : ℝ) (hlam : 0 < lam) (hT0 : 0 < T) (hT1 : T ≤ 1) :
    let f : ℝ → ℝ → ℝ := fun p1 p2 =>
      p2 * lam * Real.exp (-p2) + (p1 - p2) * lam * T * Real.exp (-p1)
    let p1star : ℝ := 2 - T / Real.exp 1
    let p2star : ℝ := p1star - 1
    p2star ≤ p1star ∧
    f p1star p2star = lam * Real.exp (-1 + T / Real.exp 1) ∧
    (∀ p1 p2 : ℝ, p2 ≤ p1 → f p1 p2 ≤ lam * Real.exp (-1 + T / Real.exp 1)) ∧
    (∀ p1 p2 : ℝ, p2 ≤ p1 → f p1 p2 = lam * Real.exp (-1 + T / Real.exp 1) →
      p1 = p1star ∧ p2 = p2star) ∧
    1 ≤ p1star ∧ p2star ≤ 1 := by
  intro f p1star p2star
  set c : ℝ := T / Real.exp 1 with hc
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hc0 : 0 < c := div_pos hT0 hE
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one hE]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  -- generic bound
  have hbound : ∀ p1 p2 : ℝ,
      p2 * Real.exp (-p2) + T * ((p1 - p2) * Real.exp (-p1)) ≤ Real.exp (-1 + c) := by
    intro p1 p2
    have h1 := mul_le_mul_of_nonneg_left (a22a8542_A p1 p2) hT0.le
    have h2 := a22a8542_B p2 c
    have h3 := a22a8542_mid p2 T
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show p1star - 1 ≤ p1star; linarith
  · show (p1star - 1) * lam * Real.exp (-(p1star - 1))
        + (p1star - (p1star - 1)) * lam * T * Real.exp (-p1star) = lam * Real.exp (-1 + c)
    have e1 : Real.exp (-p1star) = Real.exp (-(p1star - 1) - 1) := by ring_nf
    have hp : p1star - 1 = 1 - c := by show 2 - c - 1 = 1 - c; ring
    have h3 := a22a8542_mid (p1star - 1) T
    rw [hp] at h3
    rw [e1, hp]
    have e2 : Real.exp (-(1 - c)) = Real.exp (-1 + c) := by ring_nf
    rw [e2] at h3
    have e3 : (1 - c + c) = 1 := by ring
    rw [e3, mul_one] at h3
    have : (1 - c) * lam * Real.exp (-(1 - c)) + (p1star - (1 - c)) * lam * T * Real.exp (-(1 - c) - 1)
        = lam * ((1 - c) * Real.exp (-(1 - c)) + T * Real.exp (-(1 - c) - 1)) := by
      have : p1star - (1 - c) = 1 := by show 2 - c - (1 - c) = 1; ring
      rw [this]; ring
    rw [this, e2, h3]
  · intro p1 p2 _
    show p2 * lam * Real.exp (-p2) + (p1 - p2) * lam * T * Real.exp (-p1) ≤ lam * Real.exp (-1 + c)
    rw [a22a8542_f]
    exact mul_le_mul_of_nonneg_left (hbound p1 p2) hlam.le
  · intro p1 p2 _ heq
    change p2 * lam * Real.exp (-p2) + (p1 - p2) * lam * T * Real.exp (-p1)
      = lam * Real.exp (-1 + c) at heq
    rw [a22a8542_f] at heq
    have hX : p2 * Real.exp (-p2) + T * ((p1 - p2) * Real.exp (-p1)) = Real.exp (-1 + c) :=
      mul_left_cancel₀ hlam.ne' heq
    have hd : p1 - p2 = 1 := by
      by_contra hne
      have h1 := mul_lt_mul_of_pos_left (a22a8542_A_lt p1 p2 hne) hT0
      have h2 := a22a8542_B p2 c
      have h3 := a22a8542_mid p2 T
      linarith
    have hp2 : p2 = 1 - c := by
      by_contra hne
      have h1 := mul_le_mul_of_nonneg_left (a22a8542_A p1 p2) hT0.le
      have h2 := a22a8542_B_lt p2 c hne
      have h3 := a22a8542_mid p2 T
      linarith
    constructor
    · show p1 = 2 - c; linarith
    · show p2 = 2 - c - 1; linarith
  · show 1 ≤ 2 - c; linarith
  · show 2 - c - 1 ≤ 1; linarith
