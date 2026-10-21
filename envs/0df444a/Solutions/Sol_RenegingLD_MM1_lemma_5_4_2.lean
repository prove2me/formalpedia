-- Prove2me | solution 2 for RenegingLD.MM1.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:49:27.347832+00:00
-- url     : https://prove2.me/submissions/254151e1-2991-4cb0-a02d-a3df6f3d43f3

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

open RenegingLD.MM1
open MeasureTheory Filter Topology
open scoped ENNReal

theorem solution (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (γ x0 T : ℝ) (hγ : 0 < γ) (hx0 : 0 ≤ x0) (hT : 0 < T)
    (A B : ℝ) (hA : A < Real.exp (-θ * T)) (h59 : eq59 lam mu θ γ x0 T A)
    (hB : B = 1 / (1 - A * Real.exp (θ * T))) :
    zetaBar lam mu θ x0 A B T = γ * T := by
  -- basic quantities
  have he1 : Real.exp (-θ * T) < 1 := by
    have := Real.exp_lt_exp.2 (show -θ * T < 0 by nlinarith)
    simpa using this
  have hA1 : A < 1 := hA.trans he1
  have h1A : 0 < 1 - A := by linarith
  have hprod : Real.exp (-θ * T) * Real.exp (θ * T) = 1 := by
    rw [← Real.exp_add]; simp
  have hepos : 0 < Real.exp (θ * T) := Real.exp_pos _
  have hden : 0 < 1 - A * Real.exp (θ * T) := by
    have : A * Real.exp (θ * T) < Real.exp (-θ * T) * Real.exp (θ * T) :=
      mul_lt_mul_of_pos_right hA hepos
    linarith
  have hBpos : 0 < B := by rw [hB]; exact one_div_pos.2 hden
  set Λ := Lam θ A T with hΛ
  have hΛpos : 0 < Λ := by
    simp only [hΛ, Lam]; exact div_pos (by linarith) h1A
  set c := θ * T - 1 + Real.exp (-θ * T) with hc
  have hcpos : 0 < c := by
    have := Real.add_one_le_exp (-θ * T)
    have h' : Real.exp (-θ * T) ≠ -θ * T + 1 := by
      intro h
      have := (Real.add_one_lt_exp (x := -θ * T) (by nlinarith))
      linarith
    have := lt_of_le_of_ne this (Ne.symm h')
    simp only [hc]; linarith
  set d := Real.log Λ - Λ + 1 with hd
  have hdle : d ≤ 0 := by
    have := Real.log_le_sub_one_of_pos hΛpos
    simp only [hd]; linarith
  set g := γ * T - x0 + x0 * Λ with hg
  -- from (5.9): B is the larger root of λ c B² − θ g B + µ d = 0
  have hB59 : B = 1 / (2 * lam * c) * (θ * g + Real.sqrt (θ ^ 2 * g ^ 2 - 4 * lam * c * mu * d)) := by
    rw [hB]; exact h59
  have harg : 0 ≤ θ ^ 2 * g ^ 2 - 4 * lam * c * mu * d := by
    have : 0 ≤ lam * c * mu * (-d) := by
      apply mul_nonneg (mul_nonneg (mul_nonneg hlam.le hcpos.le) hmu.le); linarith
    nlinarith [sq_nonneg (θ * g)]
  have hs := Real.sq_sqrt harg
  set s := Real.sqrt (θ ^ 2 * g ^ 2 - 4 * lam * c * mu * d) with hs_def
  have hlc : 0 < 2 * lam * c := by positivity
  have hBs : 2 * lam * c * B - θ * g = s := by
    rw [hB59]; field_simp; ring
  have hquad : lam * c * B ^ 2 - θ * g * B + mu * d = 0 := by
    have h2 : (2 * lam * c * B - θ * g) ^ 2 = θ ^ 2 * g ^ 2 - 4 * lam * c * mu * d := by
      rw [hBs, hs]
    have h4 : 4 * (lam * c) * (lam * c * B ^ 2 - θ * g * B + mu * d) = 0 := by
      linear_combination h2
    have : 4 * (lam * c) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h4).resolve_left this
  -- divide by θ B
  have hkey : lam * B / θ * c + mu / (θ * B) * d = g := by
    field_simp
    linear_combination hquad
  -- assemble
  have hz : zetaBar lam mu θ x0 A B T =
      (lam * B / θ * c + mu / (θ * B) * d) + (1 - Real.exp (-θ * T)) / (1 - A) * x0 := by
    simp only [zetaBar, hc, hd, hΛ, Lam]
  rw [hz, hkey, hg]
  have : (1 - Real.exp (-θ * T)) / (1 - A) = 1 - Λ := by
    simp only [hΛ, Lam]; field_simp; ring
  rw [this]; ring
