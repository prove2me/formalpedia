-- Prove2me | solution 1 for PI.FdFjNearSup.W.fj_pnorm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:17.630594+00:00
-- url     : https://prove2.me/submissions/a9d46a14-b483-4800-8fe9-7e8a19336fce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf
import Theorems.Thm_PI_FdFjNearSup_W_nfac_pos
import Theorems.Thm_PI_FdFjNearSup_W_pnorm_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FdFjNearSup PI.FdFjNearSup.W
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace PI.FdFjNearSup.W
theorem _root_.solution {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hflow : ∀ x ∈ X.dom, ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom ∧
      X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x)
    (hP : ∀ x ∈ X.dom, X.pnorm la P x ≤ C) :
    ∀ x ∈ X.dom, X.pnorm la (X.fj la ξ ν P) x ≤ C := by
  intro x hx
  have hn := nfac_pos X la hx

  have hexp : ∀ s : X.Ψ → ℝ, ‖cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ))‖ = 1 := by
    intro s
    have e : -(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ) =
        ((-(4 * Real.pi * ∑ τ, ν τ * s τ) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [e, Complex.norm_exp_ofReal_mul_I]
  have hbound : ∀ s : X.Ψ → ℝ, ‖P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ))‖ ≤ C / X.nfac la x := by
    intro s
    obtain ⟨hd, hnf⟩ := hflow x hx s
    have h1 := hP _ hd
    rw [pnorm_eq, hnf] at h1
    rw [norm_mul, hexp s, mul_one, le_div_iff₀ hn]
    exact h1
  rw [pnorm_eq]
  unfold Data.fj
  split_ifs with h₁ h₂
  · obtain ⟨-, -, hpos, hfin⟩ := h₂.choose_spec
    have hV : 0 < (volume h₂.choose).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
    have hint := norm_setIntegral_le_of_norm_le_const hfin (fun s _ => hbound s)
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV]
    have hreal : volume.real h₂.choose = (volume h₂.choose).toReal := rfl
    rw [hreal] at hint
    calc (volume h₂.choose).toReal⁻¹ * ‖∫ s in h₂.choose, P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
          cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ))‖ * X.nfac la x
        ≤ (volume h₂.choose).toReal⁻¹ * (C / X.nfac la x * (volume h₂.choose).toReal) *
          X.nfac la x := by gcongr
      _ = C := by field_simp
  · simpa using hC0
  · simpa using hC0
end PI.FdFjNearSup.W
