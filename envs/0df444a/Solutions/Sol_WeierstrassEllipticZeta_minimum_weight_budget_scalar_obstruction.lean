-- Prove2me | solution 1 for WeierstrassEllipticZeta.minimum_weight_budget_scalar_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-23T03:11:34.714574+00:00
-- url     : https://prove2.me/submissions/41638f86-487c-41ce-bf6e-ee216afafdee

import Theorems.Thm_WeierstrassEllipticZeta_fibre_present_minimum_anchor_weight
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_first_chart_birelation_dimension
import Mathlib.Tactic
import Definitions.Def_WeierstrassEllipticZeta_OptimalAnchorWeight
import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
open WeierstrassEllipticZeta
open scoped Classical

theorem solution
    (L : PeriodPair) (η : L.lattice →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n U E : ℕ) (K : Set ℂ) (Z : Finset ℂ) (C : ℝ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hC : 0 ≤ C)
    (hcontact : U + 1 ≤ E)
    (hbudget : (((minimumAnchorWeight L.lattice η X S Q m n K Z * E : ℕ) : ℝ)
      ≤ C * (Module.finrank ℂ (firstChartSectionSpace L m n) : ℝ))) :
    ((U + 1 : ℕ) : ℝ) * (X.card : ℝ) ≤ (10 * C) * (m : ℝ) * (n : ℝ) ^ 2 ∨
    ((U + 1 : ℕ) : ℝ) * ((X.image L.lattice.mkQ).card : ℝ) ≤
      (5 * C) * (n : ℝ) ^ 2 := by
  have hmin := (fibre_present_minimum_anchor_weight L.lattice η X S Q m n K Z).1
  have hdim := (elliptic_first_chart_birelation_dimension L m n hn).2.2
  have hsmall := Nat.mul_le_mul hmin hcontact
  have hbound : (((min X.card ((m + 1) * (X.image L.lattice.mkQ).card) *
      (U + 1) : ℕ) : ℝ)) ≤ C * ((5 * (m + 1) * n ^ 2 : ℕ) : ℝ) := by
    calc
      _ ≤ (((minimumAnchorWeight L.lattice η X S Q m n K Z * E : ℕ) : ℝ)) := by
        exact_mod_cast hsmall
      _ ≤ C * (Module.finrank ℂ (firstChartSectionSpace L m n) : ℝ) := hbudget
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hdim) hC
  by_cases hpoint : X.card ≤ (m + 1) * (X.image L.lattice.mkQ).card
  · left
    push_cast
    rw [Nat.min_eq_left hpoint] at hbound
    push_cast at hbound
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm2 : (m : ℝ) + 1 ≤ 2 * m := by linarith
    calc
      _ ≤ C * (5 * ((m : ℝ) + 1) * (n : ℝ) ^ 2) := by nlinarith [hbound]
      _ ≤ C * (5 * (2 * (m : ℝ)) * (n : ℝ) ^ 2) := by gcongr
      _ = _ := by ring
  · right
    push_cast
    rw [Nat.min_eq_right (by omega)] at hbound
    push_cast at hbound
    have hmpos : 0 < (m : ℝ) + 1 := by positivity
    apply (mul_le_mul_iff_right₀ hmpos).mp
    nlinarith [hbound]
