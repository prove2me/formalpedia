-- Prove2me | solution 1 for ReynoldsNumber.viscous_coefficient_eq_inv_Re
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T20:10:58.881797+00:00
-- url     : https://prove2.me/submissions/6749cd2c-ab04-4933-beb2-2a5439d4ed9e

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_ReynoldsNumber_core

open ReynoldsNumber

theorem W2p_ReynoldsNumber_dimensionless_iff_mem_span (a b c d : ℝ) :
    Dimensionless a b c d ↔ ∃ s : ℝ, (a, b, c, d) = (s, s, s, -s) := by
  unfold Dimensionless dimExponents
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨a, rfl, by linarith, by linarith, by linarith⟩
  · rintro ⟨s, rfl, rfl, rfl, rfl⟩
    refine ⟨by ring, by ring, by ring⟩

theorem W2p_ReynoldsNumber_dimensionless_iff_rpow_Re (rho u L mu : ℝ) (hrho : 0 < rho)
    (hu : 0 < u) (hL : 0 < L) (hmu : 0 < mu) (a b c d : ℝ) :
    Dimensionless a b c d ↔
      ∃ s : ℝ, (a, b, c, d) = (s, s, s, -s) ∧
        rho ^ a * u ^ b * L ^ c * mu ^ d = Re rho u L mu ^ s := by
  rw [W2p_ReynoldsNumber_dimensionless_iff_mem_span]
  constructor
  · rintro ⟨s, h⟩
    refine ⟨s, h, ?_⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    unfold Re
    rw [Real.div_rpow (by positivity) hmu.le, Real.mul_rpow (by positivity) hL.le,
      Real.mul_rpow hrho.le hu.le, Real.rpow_neg hmu.le]
    ring
  · rintro ⟨s, h, -⟩
    exact ⟨s, h⟩

theorem solution (rho V L mu : ℝ) (hrho : 0 < rho)
    (hV : 0 < V) (hL : 0 < L) (hmu : 0 < mu) : mu / (rho * L * V) = 1 / Re rho V L mu := by
  unfold Re
  rw [one_div_div]
  ring

theorem W2p_ReynoldsNumber_hydraulicDiameter_annulus (Do Di A P : ℝ) (hDi : 0 < Di)
    (hDo : Di < Do)
    (hA : A = Real.pi * (Do ^ 2 - Di ^ 2) / 4) (hP : P = Real.pi * (Do + Di)) :
    hydraulicDiameter A P = Do - Di := by
  subst hA hP
  unfold hydraulicDiameter
  have h1 : Do + Di ≠ 0 := (by linarith : (0:ℝ) < Do + Di).ne'
  have h2 := Real.pi_pos.ne'
  field_simp <;> ring

theorem W2p_ReynoldsNumber_hydraulicDiameter_circular (D A P : ℝ) (hD : 0 < D)
    (hA : A = Real.pi * D ^ 2 / 4)
    (hP : P = Real.pi * D) : hydraulicDiameter A P = D := by
  subst hA hP
  unfold hydraulicDiameter
  have h1 : D ≠ 0 := hD.ne'
  have h2 := Real.pi_pos.ne'
  field_simp <;> ring

theorem W2p_ReynoldsNumber_re_pipe_volumetric_and_mass_flow (rho Q A DH mu : ℝ)
    (hrho : 0 < rho)
    (hA : 0 < A) (hmu : 0 < mu) :
    Re rho (Q / A) DH mu = Q * DH / (kinematicViscosity mu rho * A) ∧
      Re rho (Q / A) DH mu = rho * Q * DH / (mu * A) := by
  unfold Re kinematicViscosity
  have := hrho.ne'
  have := hA.ne'
  have := hmu.ne'
  constructor
  · field_simp <;> ring
  · field_simp <;> ring

theorem W2p_ReynoldsNumber_re_eq_mul_div_kinematicViscosity (rho u L mu : ℝ) (hrho : 0 < rho)
    (hmu : 0 < mu) :
    Re rho u L mu = u * L / kinematicViscosity mu rho := by
  unfold Re kinematicViscosity
  rw [div_div_eq_mul_div]
  ring

theorem W2p_ReynoldsNumber_re_unit_scale_invariant (m l t rho u L mu : ℝ) (hm : 0 < m)
    (hl : 0 < l)
    (ht : 0 < t) (hrho : 0 < rho) (hL : 0 < L) (hmu : 0 < mu) :
    Re (rho * m / l ^ 3) (u * l / t) (L * l) (mu * m / (l * t)) = Re rho u L mu := by
  unfold Re
  have := hm.ne'
  have := hl.ne'
  have := ht.ne'
  have := hmu.ne'
  field_simp <;> ring
