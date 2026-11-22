-- Prove2me | solution 1 for StationaryBwK.ratio_minimization
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T06:08:14.735255+00:00
-- url     : https://prove2.me/submissions/0e50e839-941b-496c-a4fb-165d8031fdc7

import Mathlib

theorem solution (ρ σr σc : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hσr₀ : 0 ≤ σr)
    (hσr₁ : σr ≤ 1) (hσc₀ : 0 ≤ σc) (hσc₁ : σc ≤ 1) :
    (∀ x ∈ Set.Ioc (0 : ℝ) 1,
      max ρ (σc * x) * (1 + σr * (1 - x) / x) =
        max (ρ + ρ * σr * (1 - x) / x) (σr * σc + σc * x * (1 - σr))) ∧
    (0 < σc →
      AntitoneOn (fun x : ℝ => max ρ (σc * x) * (1 + σr * (1 - x) / x))
          (Set.Ioc 0 (min 1 (ρ / σc))) ∧
        MonotoneOn (fun x : ℝ => max ρ (σc * x) * (1 + σr * (1 - x) / x))
          (Set.Icc (ρ / σc) 1)) ∧
    (ρ ≤ σc →
      max ρ (σc * (ρ / σc)) * (1 + σr * (1 - ρ / σc) / (ρ / σc)) = ρ + σr * (σc - ρ)) ∧
    (∀ x ∈ Set.Ioc (0 : ℝ) 1,
      ρ + σr * max (σc - ρ) 0 ≤ max ρ (σc * x) * (1 + σr * (1 - x) / x)) := by
  -- nonnegativity of the factor `1 + σr * (1 - x) / x` for `0 < x ≤ 1`
  have hdle : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 ≤ 1 + σr * (1 - x) / x := by
    intro x hx hx1
    have h1 : 0 ≤ σr * (1 - x) := mul_nonneg hσr₀ (by linarith)
    have h2 : 0 ≤ σr * (1 - x) / x := div_nonneg h1 hx.le
    linarith
  have key1 : ∀ x : ℝ, 0 < x →
      ρ + ρ * σr * (1 - x) / x - (σr * σc + σc * x * (1 - σr)) =
        (ρ - σc * x) * (1 + σr * (1 - x) / x) := by
    intro x hx
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- conjunct 1
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hd := hdle x hx0 hx1
    rcases le_total (σc * x) ρ with h | h
    · have hρmax : max ρ (σc * x) = ρ := max_eq_left h
      have h2 : max (ρ + ρ * σr * (1 - x) / x) (σr * σc + σc * x * (1 - σr)) =
          ρ + ρ * σr * (1 - x) / x := by
        apply max_eq_left
        have h3 : 0 ≤ (ρ - σc * x) * (1 + σr * (1 - x) / x) := mul_nonneg (by linarith) hd
        have h4 := key1 x hx0
        linarith
      rw [hρmax, h2]
      field_simp
    · have hρmax : max ρ (σc * x) = σc * x := max_eq_right h
      have h2 : max (ρ + ρ * σr * (1 - x) / x) (σr * σc + σc * x * (1 - σr)) =
          σr * σc + σc * x * (1 - σr) := by
        apply max_eq_right
        have h3 : (ρ - σc * x) * (1 + σr * (1 - x) / x) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hd
        have h4 := key1 x hx0
        linarith
      rw [hρmax, h2]
      field_simp
      ring
  · -- conjunct 2
    intro hσc
    constructor
    · -- antitone on Ioc 0 (min 1 (ρ/σc))
      intro x hx y hy hxy
      show max ρ (σc * y) * (1 + σr * (1 - y) / y) ≤ max ρ (σc * x) * (1 + σr * (1 - x) / x)
      have hx0 : 0 < x := hx.1
      have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
      have hxc : σc * x ≤ ρ := by
        have h1 : x ≤ ρ / σc := le_trans hx.2 (min_le_right _ _)
        rw [le_div_iff₀ hσc] at h1
        linarith
      have hyc : σc * y ≤ ρ := by
        have h1 : y ≤ ρ / σc := le_trans hy.2 (min_le_right _ _)
        rw [le_div_iff₀ hσc] at h1
        linarith
      have hxmax : max ρ (σc * x) = ρ := max_eq_left hxc
      have hymax : max ρ (σc * y) = ρ := max_eq_left hyc
      rw [hymax, hxmax]
      have hdiv : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hxy
      have e1 : σr * (1 - y) / y = σr * (1 / y - 1) := by field_simp
      have e2 : σr * (1 - x) / x = σr * (1 / x - 1) := by field_simp
      have h3 : σr * (1 - y) / y ≤ σr * (1 - x) / x := by
        rw [e1, e2]
        nlinarith [hσr₀, hdiv]
      have h4 : ρ * (1 + σr * (1 - y) / y) ≤ ρ * (1 + σr * (1 - x) / x) := by
        apply mul_le_mul_of_nonneg_left _ hρ₀.le
        linarith
      linarith
    · -- monotone on Icc (ρ/σc) 1
      intro x hx y hy hxy
      show max ρ (σc * x) * (1 + σr * (1 - x) / x) ≤ max ρ (σc * y) * (1 + σr * (1 - y) / y)
      have hxc : ρ ≤ σc * x := by
        have h1 : ρ / σc ≤ x := hx.1
        rw [div_le_iff₀ hσc] at h1
        linarith
      have hyc : ρ ≤ σc * y := by
        have h1 : ρ / σc ≤ y := hy.1
        rw [div_le_iff₀ hσc] at h1
        linarith
      have hxmax : max ρ (σc * x) = σc * x := max_eq_right hxc
      have hymax : max ρ (σc * y) = σc * y := max_eq_right hyc
      rw [hxmax, hymax]
      have hx0 : 0 < x := lt_of_lt_of_le (div_pos hρ₀ hσc) hx.1
      have hy0 : 0 < y := lt_of_lt_of_le (div_pos hρ₀ hσc) hy.1
      have e1 : σc * x * (1 + σr * (1 - x) / x) = σc * σr + σc * x * (1 - σr) := by
        field_simp
        ring
      have e2 : σc * y * (1 + σr * (1 - y) / y) = σc * σr + σc * y * (1 - σr) := by
        field_simp
        ring
      rw [e1, e2]
      have h4 : 0 ≤ σc * (1 - σr) := mul_nonneg hσc₀ (by linarith)
      nlinarith
  · -- conjunct 3
    intro hρσc
    have hσcpos : 0 < σc := lt_of_lt_of_le hρ₀ hρσc
    have h1 : σc * (ρ / σc) = ρ := by field_simp
    rw [h1, max_self]
    have h2 : 1 + σr * (1 - ρ / σc) / (ρ / σc) = 1 + σr * (σc - ρ) / ρ := by
      field_simp
    rw [h2]
    field_simp
  · -- conjunct 4
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hd := hdle x hx0 hx1
    rcases le_total σc ρ with h | h
    · -- σc ≤ ρ
      have h0 : max (σc - ρ) 0 = 0 := max_eq_right (by linarith)
      rw [h0, mul_zero, add_zero]
      have h1 : ρ ≤ max ρ (σc * x) := le_max_left _ _
      have h2 : 1 ≤ 1 + σr * (1 - x) / x := by
        have h3 : 0 ≤ σr * (1 - x) / x := div_nonneg (mul_nonneg hσr₀ (by linarith)) hx0.le
        linarith
      calc ρ = ρ * 1 := by ring
        _ ≤ max ρ (σc * x) * (1 + σr * (1 - x) / x) := by
            exact mul_le_mul h1 h2 (by norm_num) (le_trans hρ₀.le h1)
    · -- ρ ≤ σc
      have hσcpos : 0 < σc := lt_of_lt_of_le hρ₀ h
      have h0 : max (σc - ρ) 0 = σc - ρ := max_eq_left (by linarith)
      rw [h0]
      rcases le_total (σc * x) ρ with h' | h'
      · have h1 : max ρ (σc * x) = ρ := max_eq_left h'
        rw [h1]
        have e : ρ * (1 + σr * (1 - x) / x) - (ρ + σr * (σc - ρ)) =
            σr * (ρ - σc * x) / x := by
          field_simp
          ring
        have h3 : 0 ≤ σr * (ρ - σc * x) / x :=
          div_nonneg (mul_nonneg hσr₀ (by linarith)) hx0.le
        linarith
      · have h1 : max ρ (σc * x) = σc * x := max_eq_right h'
        rw [h1]
        have e : σc * x * (1 + σr * (1 - x) / x) - (ρ + σr * (σc - ρ)) =
            (1 - σr) * (σc * x - ρ) := by
          field_simp
          ring
        have h3 : 0 ≤ (1 - σr) * (σc * x - ρ) := mul_nonneg (by linarith) (by linarith)
        linarith
