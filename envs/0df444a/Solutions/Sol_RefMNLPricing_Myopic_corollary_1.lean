-- Prove2me | solution 1 for RefMNLPricing.Myopic.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:15:41.416554+00:00
-- url     : https://prove2.me/submissions/1c9c542e-1b62-47b6-8bda-8693401b935c

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model
import Definitions.Def_RefMNLPricing_Myopic_Equation13

set_option autoImplicit false

open RefMNLPricing.Myopic

lemma rm_piece3 (g f1 f2 f3 : ℝ → ℝ) (α β : ℝ) (hαβ : α ≤ β)
    (h1 : Antitone f1) (h2 : Antitone f2) (h3 : Antitone f3)
    (hα : f2 α ≤ f3 α) (hβ : f1 β ≤ f2 β)
    (hg : ∀ x, g x = if x < α then f3 x else if x ≤ β then f2 x else f1 x) : Antitone g := by
  intro x x' hxx'
  rw [hg x, hg x']
  by_cases hx : x < α
  · rw [if_pos hx]
    by_cases hx' : x' < α
    · rw [if_pos hx']; exact h3 hxx'
    · rw [if_neg hx']
      by_cases hx'' : x' ≤ β
      · rw [if_pos hx'']
        calc f2 x' ≤ f2 α := h2 (not_lt.1 hx')
          _ ≤ f3 α := hα
          _ ≤ f3 x := h3 hx.le
      · rw [if_neg hx'']
        calc f1 x' ≤ f1 β := h1 (not_le.1 hx'').le
          _ ≤ f2 β := hβ
          _ ≤ f2 α := h2 hαβ
          _ ≤ f3 α := hα
          _ ≤ f3 x := h3 hx.le
  · rw [if_neg hx]
    have hx' : ¬ x' < α := fun h => hx (lt_of_le_of_lt hxx' h)
    rw [if_neg hx']
    by_cases hxb : x ≤ β
    · rw [if_pos hxb]
      by_cases hxb' : x' ≤ β
      · rw [if_pos hxb']; exact h2 hxx'
      · rw [if_neg hxb']
        calc f1 x' ≤ f1 β := h1 (not_le.1 hxb').le
          _ ≤ f2 β := hβ
          _ ≤ f2 x := h2 hxb
    · rw [if_neg hxb]
      have : ¬ x' ≤ β := fun h => hxb (hxx'.trans h)
      rw [if_neg this]; exact h1 hxx'

lemma rm_piece2 (g f1 f2 : ℝ → ℝ) (β : ℝ)
    (h1 : Antitone f1) (h2 : Antitone f2) (hβ : f1 β ≤ f2 β)
    (hg : ∀ x, g x = if x ≤ β then f2 x else f1 x) : Antitone g := by
  intro x x' hxx'
  rw [hg x, hg x']
  by_cases hxb : x ≤ β
  · rw [if_pos hxb]
    by_cases hxb' : x' ≤ β
    · rw [if_pos hxb']; exact h2 hxx'
    · rw [if_neg hxb']
      calc f1 x' ≤ f1 β := h1 (not_le.1 hxb').le
        _ ≤ f2 β := hβ
        _ ≤ f2 x := h2 hxb
  · rw [if_neg hxb]
    have : ¬ x' ≤ β := fun h => hxb (hxx'.trans h)
    rw [if_neg this]; exact h1 hxx'

lemma rm_expanti (A B C D : ℝ) (hB : 0 < B) :
    Antitone (fun v : ℝ => 1 / B * Real.exp (A - B * v + C * D - 1)) := by
  intro x x' hxx'
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  nlinarith

lemma rm_lam (A B P M R : ℝ) (hB : 0 < B) (hP : 0 ≤ P) (hM : 0 ≤ M) (h : P < M) :
    Antitone (fun v : ℝ =>
      (if R < v + 1 / (B + M) then 1 / (B + M) * Real.exp (A - (B + M) * v + M * R - 1) else 0) +
      (if v + 1 / (B + M) ≤ R ∧ R ≤ v + 1 / (B + P) then (R - v) * Real.exp (A - B * R) else 0) +
      (if v + 1 / (B + P) < R then 1 / (B + P) * Real.exp (A - (B + P) * v + P * R - 1) else 0)) := by
  have hBP : 0 < B + P := by linarith
  have hBM : 0 < B + M := by linarith
  have hu : 1 / (B + M) < 1 / (B + P) := one_div_lt_one_div_of_lt hBP (by linarith)
  have hu0 : 0 < 1 / (B + M) := by positivity
  have hw : (B + P) * (1 / (B + P)) = 1 := mul_one_div_cancel hBP.ne'
  have hu1 : (B + M) * (1 / (B + M)) = 1 := mul_one_div_cancel hBM.ne'
  refine rm_piece3 _ (fun v => 1 / (B + M) * Real.exp (A - (B + M) * v + M * R - 1))
    (fun v => (R - v) * Real.exp (A - B * R))
    (fun v => 1 / (B + P) * Real.exp (A - (B + P) * v + P * R - 1))
    (R - 1 / (B + P)) (R - 1 / (B + M)) (by linarith)
    (rm_expanti A (B + M) M R hBM) ?_ (rm_expanti A (B + P) P R hBP) ?_ ?_ ?_
  · intro x x' hxx'
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · show (R - (R - 1 / (B + P))) * Real.exp (A - B * R) ≤
      1 / (B + P) * Real.exp (A - (B + P) * (R - 1 / (B + P)) + P * R - 1)
    have : A - (B + P) * (R - 1 / (B + P)) + P * R - 1 = A - B * R := by linear_combination hw
    rw [this]; apply le_of_eq; ring_nf
  · show 1 / (B + M) * Real.exp (A - (B + M) * (R - 1 / (B + M)) + M * R - 1) ≤
      (R - (R - 1 / (B + M))) * Real.exp (A - B * R)
    have : A - (B + M) * (R - 1 / (B + M)) + M * R - 1 = A - B * R := by linear_combination hu1
    rw [this]; apply le_of_eq; ring_nf
  · intro x
    by_cases h3 : x < R - 1 / (B + P)
    · rw [if_pos h3]
      rw [if_neg (show ¬ (R < x + 1 / (B + M)) by linarith),
        if_neg (show ¬ (x + 1 / (B + M) ≤ R ∧ R ≤ x + 1 / (B + P)) by
          rintro ⟨_, h⟩; linarith),
        if_pos (show x + 1 / (B + P) < R by linarith)]
      simp
    · rw [if_neg h3]
      by_cases h2 : x ≤ R - 1 / (B + M)
      · rw [if_pos h2]
        rw [if_neg (show ¬ (R < x + 1 / (B + M)) by linarith),
          if_pos (show x + 1 / (B + M) ≤ R ∧ R ≤ x + 1 / (B + P) from ⟨by linarith, by linarith⟩),
          if_neg (show ¬ (x + 1 / (B + P) < R) by linarith)]
        simp
      · rw [if_neg h2]
        rw [if_pos (show R < x + 1 / (B + M) by linarith),
          if_neg (show ¬ (x + 1 / (B + M) ≤ R ∧ R ≤ x + 1 / (B + P)) by
            rintro ⟨h, _⟩; linarith),
          if_neg (show ¬ (x + 1 / (B + P) < R) by linarith)]
        simp

lemma rm_gam (A B P M R Z : ℝ) (hB : 0 < B) (hP : 0 ≤ P) (hM : 0 ≤ M) (h : M < P)
    (hZ : Z = (Real.log (B + P) - Real.log (B + M)) / (P - M)) :
    Antitone (fun v : ℝ =>
      (if R < v + Z then 1 / (B + M) * Real.exp (A - (B + M) * v + M * R - 1) else 0) +
      (if v + Z ≤ R then 1 / (B + P) * Real.exp (A - (B + P) * v + P * R - 1) else 0)) := by
  have hBP : 0 < B + P := by linarith
  have hBM : 0 < B + M := by linarith
  refine rm_piece2 _ (fun v => 1 / (B + M) * Real.exp (A - (B + M) * v + M * R - 1))
    (fun v => 1 / (B + P) * Real.exp (A - (B + P) * v + P * R - 1)) (R - Z)
    (rm_expanti A (B + M) M R hBM) (rm_expanti A (B + P) P R hBP) ?_ ?_
  · show 1 / (B + M) * Real.exp (A - (B + M) * (R - Z) + M * R - 1) ≤
      1 / (B + P) * Real.exp (A - (B + P) * (R - Z) + P * R - 1)
    have hPM : P - M ≠ 0 := by linarith
    have hZ' : (P - M) * Z = Real.log (B + P) - Real.log (B + M) := by
      rw [hZ]; field_simp
    have e1 : ∀ (X C : ℝ) (hC : 0 < C), 1 / C * Real.exp X = Real.exp (X - Real.log C) := by
      intro X C hC
      rw [Real.exp_sub, Real.exp_log hC]; ring
    rw [e1 _ _ hBM, e1 _ _ hBP]
    apply Real.exp_le_exp.2
    nlinarith [hZ']
  · intro x
    by_cases hx : x ≤ R - Z
    · rw [if_pos hx, if_neg (show ¬ (R < x + Z) by linarith),
        if_pos (show x + Z ≤ R by linarith)]
      simp
    · rw [if_neg hx, if_pos (show R < x + Z by linarith),
        if_neg (show ¬ (x + Z ≤ R) by linarith)]
      simp

theorem solution {n : ℕ} (a b cp cm : Fin n → ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i) (r : Fin n → ℝ) :
    Antitone (fun v : ℝ => rhs13 a b cp cm v r) := by
  intro x x' hxx'
  unfold rhs13
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases h1 : cp i < cm i
  · simp only [if_pos h1]
    exact rm_lam (a i) (b i) (cp i) (cm i) (r i) (hb i) (hcp i) (hcm i) h1 hxx'
  · by_cases h2 : cp i = cm i
    · simp only [if_neg h1, if_pos h2]
      exact rm_expanti (a i) (b i + cp i) (cp i) (r i) (by linarith [hb i, hcp i]) hxx'
    · simp only [if_neg h1, if_neg h2]
      have h3 : cm i < cp i := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
      exact rm_gam (a i) (b i) (cp i) (cm i) (r i) (Zgap b cp cm i) (hb i) (hcp i) (hcm i) h3 rfl hxx'
