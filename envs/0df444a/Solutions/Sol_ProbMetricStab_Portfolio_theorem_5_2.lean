-- Prove2me | solution 1 for ProbMetricStab.Portfolio.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:30:46.834199+00:00
-- url     : https://prove2.me/submissions/26a356ff-62ea-4df3-9882-8ba619228f87

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting
import Theorems.Thm_ProbMetricStab_Portfolio_risk_lipschitz

open MeasureTheory
open scoped ENNReal
open ProbMetricStab.Portfolio

theorem solution {s : ℕ} (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (Γ : Measure (Rs s))
    (hΓ : IsSpectral Γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (α' : ℝ) (Γ' : Measure (Rs s)), 1 < α' → α' < 2 → IsSpectral Γ' →
      zeta1 Γ Γ' + ENNReal.ofReal |α - α'| < ENNReal.ofReal δ →
      ∀ x ∈ solSet α' Γ',
        Metric.infEDist x (solSet α Γ)
          ≤ Psi α Γ (α * (zeta1 Γ Γ').toReal + Real.exp (-1) * |α - α'|) := by
  refine ⟨1, one_pos, ?_⟩
  intro α' Γ' h1 h2 hΓ' hsmall x hx
  have hζ : zeta1 Γ Γ' ≠ ⊤ := by
    intro h
    rw [h, top_add] at hsmall
    exact not_top_lt hsmall
  have hα0 : 0 ≤ α := by linarith
  set η := α * (zeta1 Γ Γ').toReal + Real.exp (-1) * |α - α'| with hη
  have hη0 : 0 ≤ η :=
    add_nonneg (mul_nonneg hα0 ENNReal.toReal_nonneg) (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
  have hbound : ∀ y ∈ simplex s, |risk α Γ y - risk α' Γ' y| ≤ η := by
    intro y hy
    have h := risk_lipschitz α α' hα1 hα2 h1 h2 Γ Γ' hΓ hΓ' y hy
    have heq : ENNReal.ofReal α * zeta1 Γ Γ' + ENNReal.ofReal (Real.exp (-1) * |α - α'|)
        = ENNReal.ofReal η := by
      rw [hη, ENNReal.ofReal_add (mul_nonneg hα0 ENNReal.toReal_nonneg)
        (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)), ENNReal.ofReal_mul hα0,
        ENNReal.ofReal_toReal hζ]
    rw [heq] at h
    exact (ENNReal.ofReal_le_ofReal_iff hη0).1 h
  have hxX := hx.1
  have hgap : risk α Γ x - optVal α Γ ≤ 2 * η := by
    have hne : (risk α Γ '' simplex s).Nonempty := ⟨_, x, hxX, rfl⟩
    have : risk α Γ x - 2 * η ≤ optVal α Γ := by
      unfold optVal
      apply le_csInf hne
      rintro _ ⟨y, hy, rfl⟩
      have e1 := hbound x hxX
      have e2 := hbound y hy
      have e3 := hx.2 y hy
      rw [abs_le] at e1 e2
      linarith
    linarith
  have hkey : ∀ τ : ℝ, 0 ≤ τ → ENNReal.ofReal τ ≤ Metric.infEDist x (solSet α Γ) →
      ENNReal.ofReal τ ≤ psiInv α Γ (2 * η) := by
    intro τ hτ hD
    unfold psiInv
    refine le_iSup₂_of_le (f := fun τ (_ : τ ∈ {τ : ℝ | 0 ≤ τ ∧ psi α Γ τ ≤ ((2 * η : ℝ) : EReal)}) =>
      ENNReal.ofReal τ) τ ⟨hτ, ?_⟩ le_rfl
    unfold psi
    refine (iInf₂_le x ⟨hxX, hD⟩).trans ?_
    exact EReal.coe_le_coe_iff.mpr hgap
  have hD : Metric.infEDist x (solSet α Γ) ≤ psiInv α Γ (2 * η) := by
    by_cases htop : Metric.infEDist x (solSet α Γ) = ⊤
    · have htop' : psiInv α Γ (2 * η) = ⊤ := ENNReal.eq_top_of_forall_nnreal_le fun r => by
        have := hkey r r.2 (by rw [htop]; exact le_top)
        simpa using this
      rw [htop']
      exact le_top
    · have := hkey _ ENNReal.toReal_nonneg (by rw [ENNReal.ofReal_toReal htop])
      rwa [ENNReal.ofReal_toReal htop] at this
  calc Metric.infEDist x (solSet α Γ) ≤ psiInv α Γ (2 * η) := hD
    _ ≤ Psi α Γ η := by unfold Psi; exact le_add_self
