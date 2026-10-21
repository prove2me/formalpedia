-- Prove2me | solution 1 for RenegingLD.MM1.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:46:55.511619+00:00
-- url     : https://prove2.me/submissions/0bee705b-7165-490f-96ac-60e93d862f76

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open RenegingLD.MM1

theorem solution (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (γ x0 T : ℝ) (hγ : 0 < γ) (hx0 : 0 ≤ x0) (hT : 0 < T)
    (A B : ℝ) (hA : A < Real.exp (-θ * T)) (h59 : eq59 lam mu θ γ x0 T A)
    (hB : B = 1 / (1 - A * Real.exp (θ * T))) :
    zetaBar lam mu θ x0 A B T = γ * T := by
  have hθT : 0 < θ * T := mul_pos hθ hT
  have hexp1 : Real.exp (-θ * T) < 1 := by
    have := Real.exp_lt_exp.mpr (show -θ * T < 0 by nlinarith)
    simpa using this
  have hexp0 : 0 < Real.exp (-θ * T) := Real.exp_pos _
  have hA1 : 0 < 1 - A := by linarith
  have hE : 0 < 1 - A * Real.exp (θ * T) := by
    have h1 : A * Real.exp (θ * T) < Real.exp (-θ * T) * Real.exp (θ * T) :=
      mul_lt_mul_of_pos_right hA (Real.exp_pos _)
    have h2 : Real.exp (-θ * T) * Real.exp (θ * T) = 1 := by
      rw [← Real.exp_add]; simp
    linarith
  have hBpos : 0 < B := by rw [hB]; positivity
  have hD : 0 < θ * T - 1 + Real.exp (-θ * T) := by
    have := Real.add_one_lt_exp (show (-θ * T) ≠ 0 by intro h; nlinarith)
    linarith
  have hLpos : 0 < Lam θ A T := by
    unfold Lam
    apply div_pos <;> linarith
  have hQ : Real.log (Lam θ A T) - Lam θ A T + 1 ≤ 0 := by
    have := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hLeq : (1 - Real.exp (-θ * T)) / (1 - A) = 1 - Lam θ A T := by
    unfold Lam
    field_simp
    ring
  -- abbreviations
  obtain ⟨L, hL⟩ : ∃ L, L = Lam θ A T := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = θ * T - 1 + Real.exp (-θ * T) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = Real.log L - L + 1 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = γ * T - x0 + x0 * L := ⟨_, rfl⟩
  rw [← hL] at hLeq hQ
  rw [← hQdef] at hQ
  rw [← hDdef] at hD
  unfold eq59 at h59
  rw [← hL, ← hDdef, ← hPdef, ← hQdef, ← hB] at h59
  have hrad : 0 ≤ θ ^ 2 * P ^ 2 - 4 * lam * D * mu * Q := by
    have h1 : 0 ≤ θ ^ 2 * P ^ 2 := by positivity
    have h2 : 0 ≤ -(4 * lam * D * mu * Q) := by
      have : 0 ≤ 4 * lam * D * mu := by positivity
      nlinarith
    linarith
  have hs2 := Real.sq_sqrt hrad
  have hs : Real.sqrt (θ ^ 2 * P ^ 2 - 4 * lam * D * mu * Q) = 2 * lam * D * B - θ * P := by
    have hne : (2 * lam * D) ≠ 0 := by positivity
    have h3 : 2 * lam * D * B = θ * P + Real.sqrt (θ ^ 2 * P ^ 2 - 4 * lam * D * mu * Q) := by
      rw [h59]; field_simp
    linarith
  have key : lam * D * B ^ 2 - θ * P * B = -mu * Q := by
    rw [hs] at hs2
    have hne : (4 * lam * D) ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    linear_combination hs2
  have e : mu / (θ * B) * Q = P - lam * B / θ * D := by
    have hne : θ * B ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, div_eq_iff hne]
    have : lam * B / θ * D * (θ * B) = lam * D * B ^ 2 := by
      field_simp
    linear_combination key + this
  unfold zetaBar
  have hL' : (Real.exp (-θ * T) - A) / (1 - A) = L := hL.symm
  rw [hLeq, hL', ← hDdef]
  have hP : P = γ * T - x0 * (1 - L) := by rw [hPdef]; ring
  rw [hP] at e
  rw [hQdef] at e
  linear_combination e
