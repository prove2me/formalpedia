-- Prove2me | solution 1 for RationalCompatibleValues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:52:39.86079+00:00
-- url     : https://prove2.me/submissions/034de60a-b65f-4992-8be7-8cd326b9fa4d

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_RationalCompatibleValues

set_option autoImplicit false
open scoped NNReal
theorem _root_.solution {E : Type*} [MetricSpace E] {k : ℕ}
    (pi : E → ℝ) (K : ℝ≥0) (hpi : LipschitzWith K pi) (hK : 0 < (K : ℝ))
    (e : Fin (k + 1) → E) (eps r delta : ℝ)
    (heps : 0 < eps) (heps1 : eps < 1) (hr : 0 < r)
    (hsep : ∀ j j', e j ≠ e j' → r ≤ dist (e j) (e j'))
    (hdelta : 0 < delta) (hdle : delta ≤ eps * r * (K : ℝ) / 4) :
    ∃ (c : Fin (k + 1) → ℚ) (C : ℚ),
      (1 - eps / 2) * (K : ℝ) ≤ (C : ℝ) ∧ (C : ℝ) ≤ (K : ℝ) ∧
      (∀ j, |(c j : ℝ) - (1 - eps) * pi (e j)| ≤ delta) ∧
      (∀ j j', |(c j : ℝ) - (c j' : ℝ)| ≤ (C : ℝ) * dist (e j) (e j')) := by
-- BODY
  -- Step 1: a rational grid of mesh at most `delta`.
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hdelta
  set n : ℕ := N + 1 with hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hmesh : 1 / (n : ℝ) ≤ delta := le_of_lt (by exact_mod_cast hN)
  set h : ℝ → ℚ := fun t => (⌊t * (n : ℝ)⌋ : ℚ) / (n : ℚ) with hh
  have hhapprox : ∀ t : ℝ, |((h t : ℚ) : ℝ) - t| ≤ delta := by
    intro t
    have h1 : (⌊t * (n : ℝ)⌋ : ℝ) ≤ t * (n : ℝ) := Int.floor_le _
    have h2 : t * (n : ℝ) < (⌊t * (n : ℝ)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have hcast : ((h t : ℚ) : ℝ) = (⌊t * (n : ℝ)⌋ : ℝ) / (n : ℝ) := by
      rw [hh]; push_cast; ring
    have key : |(⌊t * (n : ℝ)⌋ : ℝ) - t * (n : ℝ)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hstep : |((h t : ℚ) : ℝ) - t| ≤ 1 / (n : ℝ) := by
      rw [hcast]
      have hrw : (⌊t * (n : ℝ)⌋ : ℝ) / (n : ℝ) - t
          = ((⌊t * (n : ℝ)⌋ : ℝ) - t * (n : ℝ)) / (n : ℝ) := by field_simp
      rw [hrw, abs_div, abs_of_pos hnpos]
      gcongr
    linarith
  -- Step 2: the rational Lipschitz constant.
  have hCbtwn : (1 - eps / 2) * (K : ℝ) < (K : ℝ) := by nlinarith
  obtain ⟨C, hC1, hC2⟩ := exists_rat_btwn hCbtwn
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := by nlinarith
  refine ⟨fun j => h ((1 - eps) * pi (e j)), C, hC1.le, hC2.le, fun j => hhapprox _, ?_⟩
  -- Step 3: compatibility.
  intro j j'
  dsimp only
  by_cases he : e j = e j'
  · have : h ((1 - eps) * pi (e j)) = h ((1 - eps) * pi (e j')) := by rw [he]
    rw [this]
    simp only [sub_self, abs_zero]
    positivity
  · have hd : r ≤ dist (e j) (e j') := hsep j j' he
    have hdpos : (0 : ℝ) < dist (e j) (e j') := lt_of_lt_of_le hr hd
    set d : ℝ := dist (e j) (e j') with hdd
    set a : ℝ := ((h ((1 - eps) * pi (e j)) : ℚ) : ℝ) with hadef
    set a' : ℝ := ((h ((1 - eps) * pi (e j')) : ℚ) : ℝ) with ha'def
    have ha : |a - (1 - eps) * pi (e j)| ≤ delta := hhapprox _
    have ha' : |a' - (1 - eps) * pi (e j')| ≤ delta := hhapprox _
    have hlip : |pi (e j) - pi (e j')| ≤ (K : ℝ) * d := by
      have := hpi.dist_le_mul (e j) (e j')
      rwa [Real.dist_eq] at this
    have e1 : |a - a'| ≤ |a - (1 - eps) * pi (e j)| + |(1 - eps) * pi (e j) - a'| :=
      abs_sub_le _ _ _
    have e2 : |(1 - eps) * pi (e j) - a'|
        ≤ |(1 - eps) * pi (e j) - (1 - eps) * pi (e j')| + |(1 - eps) * pi (e j') - a'| :=
      abs_sub_le _ _ _
    have he3 : |(1 - eps) * pi (e j) - (1 - eps) * pi (e j')|
        = (1 - eps) * |pi (e j) - pi (e j')| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - eps)]
    have he4 : |(1 - eps) * pi (e j') - a'| = |a' - (1 - eps) * pi (e j')| := abs_sub_comm _ _
    have he5 : (1 - eps) * |pi (e j) - pi (e j')| ≤ (1 - eps) * ((K : ℝ) * d) :=
      mul_le_mul_of_nonneg_left hlip (by linarith)
    have he6 : 2 * delta ≤ eps * d * (K : ℝ) / 2 := by nlinarith
    have he7 : (1 - eps / 2) * (K : ℝ) * d ≤ (C : ℝ) * d :=
      mul_le_mul_of_nonneg_right hC1.le (le_of_lt hdpos)
    nlinarith [e1, e2, he3, he4, he5, he6, he7, ha, ha']
