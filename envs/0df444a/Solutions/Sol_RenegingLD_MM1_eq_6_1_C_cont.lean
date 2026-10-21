-- Prove2me | solution 1 for RenegingLD.MM1.eq_6_1_C_cont
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:39:07.20698+00:00
-- url     : https://prove2.me/submissions/8b7acbde-a75a-41ae-869d-277ac22e01c2

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

open RenegingLD.MM1
open MeasureTheory Filter Topology
open scoped ENNReal

theorem solution (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hlm : mu ≤ lam) :
    (∀ γ : ℝ, 0 ≤ γ →
      0 < z lam mu γ ∧ lam * (z lam mu γ)⁻¹ - mu * z lam mu γ - γ = 0 ∧
        ∀ w : ℝ, 0 < w → lam * w⁻¹ - mu * w - γ = 0 → w = z lam mu γ) ∧
    ContinuousOn (C lam mu) (Set.Ici 0) ∧
    C lam mu (lam - mu) = 0 := by
  -- basic facts about the square root
  have hsq : ∀ γ : ℝ, Real.sqrt (γ ^ 2 + 4 * lam * mu) ^ 2 = γ ^ 2 + 4 * lam * mu := fun γ =>
    Real.sq_sqrt (by nlinarith [sq_nonneg γ, mul_pos hlam hmu])
  have hgt : ∀ γ : ℝ, γ < Real.sqrt (γ ^ 2 + 4 * lam * mu) := by
    intro γ
    have h0 := Real.sqrt_nonneg (γ ^ 2 + 4 * lam * mu)
    nlinarith [hsq γ, mul_pos hlam hmu]
  have hgt' : ∀ γ : ℝ, -γ < Real.sqrt (γ ^ 2 + 4 * lam * mu) := by
    intro γ
    have h0 := Real.sqrt_nonneg (γ ^ 2 + 4 * lam * mu)
    nlinarith [hsq γ, mul_pos hlam hmu]
  have zpos : ∀ γ : ℝ, 0 < z lam mu γ := by
    intro γ; unfold z
    have := hgt γ
    apply div_pos <;> linarith
  -- the quadratic relation  mu z^2 + γ z - lam = 0
  have zquad : ∀ γ : ℝ, mu * z lam mu γ ^ 2 + γ * z lam mu γ - lam = 0 := by
    intro γ; unfold z
    have h := hsq γ
    set s := Real.sqrt (γ ^ 2 + 4 * lam * mu)
    field_simp
    nlinarith [h]
  refine ⟨?_, ?_, ?_⟩
  · intro γ _
    refine ⟨zpos γ, ?_, ?_⟩
    · have hz := (zpos γ).ne'
      have := zquad γ
      field_simp
      linarith
    · intro w hw hweq
      have hwq : mu * w ^ 2 + γ * w - lam = 0 := by
        field_simp at hweq
        linarith
      -- (w - z) (mu w + mu z + γ) = 0
      have hfac : (w - z lam mu γ) * (mu * w + mu * z lam mu γ + γ) = 0 := by
        nlinarith [zquad γ]
      have hpos : 0 < mu * w + mu * z lam mu γ + γ := by
        have : mu * z lam mu γ + γ = (Real.sqrt (γ ^ 2 + 4 * lam * mu) + γ) / 2 := by
          unfold z; field_simp; ring
        rw [add_assoc, this]
        have := hgt' γ
        nlinarith [mul_pos hmu hw]
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · linarith
  · have hzc : Continuous (z lam mu) := by
      unfold z
      fun_prop
    have : Continuous (C lam mu) := by
      unfold C
      refine Continuous.sub ?_ ?_
      · refine Continuous.add ?_ ?_
        · exact continuous_const.mul (continuous_const.sub (hzc.inv₀ fun γ => (zpos γ).ne'))
        · exact continuous_const.mul (continuous_const.sub hzc)
      · exact continuous_id.mul (hzc.log fun γ => (zpos γ).ne')
    exact this.continuousOn
  · have h1 : z lam mu (lam - mu) = 1 := by
      unfold z
      have : (lam - mu) ^ 2 + 4 * lam * mu = (lam + mu) ^ 2 := by ring
      rw [this, Real.sqrt_sq (by linarith)]
      field_simp
      ring
    unfold C
    rw [h1]
    simp
