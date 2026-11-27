-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.Glob.LocCellT.tauFact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:20:55.873132+00:00
-- url     : https://prove2.me/submissions/f5e0352b-804d-465b-8be4-3015af2bc766

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_LocCellT
import Theorems.Thm_PositivityTheory_Rg_Sw_Glob_LocCellT_tauFact_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.LocCellT
variable {m n : ℕ} {X : Type*} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [IsTopologicalAddGroup X]
namespace PositivityTheory.Rg.Sw.Glob.LocCellT
theorem _root_.solution (μ : Measure X) [μ.IsAddRightInvariant] (π : X → (Fin m → Fin n → ℂ)) (hπ : Continuous π)
    (s : (Fin m → Fin n → ℂ) → X) (hπs : ∀ x u, π (x + s u) = π x + u) (B : X → ℂ) (hBm : Measurable B)
    (hB : ∀ x u, B (x + s u) = B x) (ρ : (Fin m → Fin n → ℂ) → ℝ) (hρ : Continuous ρ) (hρpos : ∀ u, 0 < ρ u)
    (hint : Integrable (fun z => ρ (π z) * ‖B z‖) μ) :
    ∃ κ : ℂ, ∀ a : (Fin m → Fin n → ℂ) → ℂ, Measurable a → (∃ C, ∀ u, ‖a u‖ ≤ C * ρ u) →
      ∫ z, a (π z) * B z ∂μ = κ * ∫ u, a u := by
  have hπm : Measurable π := hπ.measurable
  let gs : Fin 4 → X → ℝ≥0 := ![fun z => Real.toNNReal (B z).re, fun z => Real.toNNReal (-(B z).re),
    fun z => Real.toNNReal (B z).im, fun z => Real.toNNReal (-(B z).im)]
  have hgm : ∀ j, Measurable (gs j) := by
    intro j
    fin_cases j
    exacts [(Complex.measurable_re.comp hBm).real_toNNReal, (Complex.measurable_re.comp hBm).neg.real_toNNReal,
      (Complex.measurable_im.comp hBm).real_toNNReal, (Complex.measurable_im.comp hBm).neg.real_toNNReal]
  have hgi : ∀ j x u, gs j (x + s u) = gs j x := by
    intro j x u
    fin_cases j <;> simp [gs, hB]
  have hgle : ∀ j z, ((gs j z : ℝ≥0) : ℝ) ≤ ‖B z‖ := by
    intro j z
    have h1 := Complex.abs_re_le_norm (B z)
    have h2 := Complex.abs_im_le_norm (B z)
    fin_cases j <;> simp only [gs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Real.coe_toNNReal', Fin.mk_one, Fin.reduceFinMk] <;>
      first
      | exact max_le (le_trans (le_abs_self _) h1) (norm_nonneg _)
      | exact max_le (le_trans (neg_le_abs _) h1) (norm_nonneg _)
      | exact max_le (le_trans (le_abs_self _) h2) (norm_nonneg _)
      | exact max_le (le_trans (neg_le_abs _) h2) (norm_nonneg _)
  have hfin : ∀ j, ∫⁻ z, ENNReal.ofReal (ρ (π z)) * gs j z ∂μ < ∞ := by
    intro j
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hint.lintegral_lt_top
    rw [show ((gs j z : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (gs j z) from (ENNReal.ofReal_coe_nnreal).symm,
      ← ENNReal.ofReal_mul (hρpos _).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hgle j z) (hρpos _).le)
  choose c hc using fun j => tauFact_nonneg μ π hπ s hπs (gs j) (hgm j) (hgi j) ρ hρ hρpos (hfin j)
  have hdec : ∀ z, B z = ((gs 0 z : ℝ) : ℂ) - ((gs 1 z : ℝ) : ℂ) + Complex.I * (((gs 2 z : ℝ) : ℂ) - ((gs 3 z : ℝ) : ℂ)) := by
    intro z
    apply Complex.ext <;> simp [gs, Real.coe_toNNReal', max_def] <;> split_ifs <;> linarith
  refine ⟨(c 0 : ℂ) - c 1 + Complex.I * ((c 2 : ℂ) - c 3), fun a ha ⟨C, hC⟩ => ?_⟩
  have hint' : ∀ j, Integrable (fun z => a (π z) * ((gs j z : ℝ≥0) : ℂ)) μ := by
    intro j
    refine Integrable.mono' (hint.const_mul C) ((ha.comp hπm).mul (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have hC0 : 0 ≤ C := by
      by_contra h
      have := hC (π z)
      nlinarith [norm_nonneg (a (π z)), hρpos (π z)]
    rw [norm_mul]
    calc ‖a (π z)‖ * ‖((gs j z : ℝ≥0) : ℂ)‖ ≤ (C * ρ (π z)) * ‖B z‖ := by
          refine mul_le_mul (hC _) ?_ (norm_nonneg _) (mul_nonneg hC0 (hρpos _).le)
          rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
          exact hgle j z
      _ = C * (ρ (π z) * ‖B z‖) := by ring
  have e : (fun z => a (π z) * B z) = fun z => (a (π z) * ((gs 0 z : ℝ≥0) : ℂ) - a (π z) * ((gs 1 z : ℝ≥0) : ℂ)) +
      Complex.I * (a (π z) * ((gs 2 z : ℝ≥0) : ℂ) - a (π z) * ((gs 3 z : ℝ≥0) : ℂ)) := by
    funext z
    rw [hdec z]
    ring
  have i01 : Integrable (fun z => a (π z) * ((gs 0 z : ℝ≥0) : ℂ) - a (π z) * ((gs 1 z : ℝ≥0) : ℂ)) μ :=
    (hint' 0).sub (hint' 1)
  have i23 : Integrable (fun z => Complex.I * (a (π z) * ((gs 2 z : ℝ≥0) : ℂ) - a (π z) * ((gs 3 z : ℝ≥0) : ℂ))) μ :=
    ((hint' 2).sub (hint' 3)).const_mul Complex.I
  rw [e, integral_add i01 i23, integral_const_mul, integral_sub (hint' 0) (hint' 1), integral_sub (hint' 2) (hint' 3)]
  have k : ∀ j, ∫ z, a (π z) * ((gs j z : ℝ≥0) : ℂ) ∂μ = (c j : ℂ) * ∫ u, a u := by
    intro j
    have := hc j a ha
    simpa using this
  rw [k 0, k 1, k 2, k 3]
  ring
end PositivityTheory.Rg.Sw.Glob.LocCellT
