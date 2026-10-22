-- Prove2me | solution 1 for StaticQuote.Clairvoyant.dyadic_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:59:45.974743+00:00
-- url     : https://prove2.me/submissions/829ab05b-434e-41b8-aca4-946ddf1da353

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting
import Theorems.Thm_StaticQuote_Clairvoyant_doubling

open MeasureTheory Filter
open scoped ENNReal
open StaticQuote.Clairvoyant

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω)
    (hQ : Q.Standing μ) (N : ℕ) (hN : 1 ≤ N) :
    Monotone (fun k : ℕ => ∫⁻ ω, Q.gamma 1 (2 ^ k * N) ω / ((2 ^ k * N : ℕ) : ℝ≥0∞) ∂μ) ∧
      ∫⁻ ω, Q.gamma 1 N ω / (N : ℝ≥0∞) ∂μ ≤
        limsup (fun k : ℕ => ∫⁻ ω, Q.gamma 1 (2 ^ k * N) ω / ((2 ^ k * N : ℕ) : ℝ≥0∞) ∂μ)
          atTop := by
  have key : ∀ M : ℕ, 1 ≤ M → ∫⁻ ω, Q.gamma 1 M ω / (M : ℝ≥0∞) ∂μ ≤
      ∫⁻ ω, Q.gamma 1 (2 * M) ω / ((2 * M : ℕ) : ℝ≥0∞) ∂μ := by
    intro M hM
    have hM0 : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    have hMt : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hM0),
      lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (by exact_mod_cast (show 2 * M ≠ 0 by omega)))]
    have hd := doubling Q hQ M
    calc (∫⁻ ω, Q.gamma 1 M ω ∂μ) * (M : ℝ≥0∞)⁻¹
        = (2 * ∫⁻ ω, Q.gamma 1 M ω ∂μ) * ((2 * M : ℕ) : ℝ≥0∞)⁻¹ := by
          push_cast
          rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
          calc (∫⁻ ω, Q.gamma 1 M ω ∂μ) * (M : ℝ≥0∞)⁻¹
              = (2 * 2⁻¹) * ((∫⁻ ω, Q.gamma 1 M ω ∂μ) * (M : ℝ≥0∞)⁻¹) := by
                rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
            _ = _ := by ring
      _ ≤ (∫⁻ ω, Q.gamma 1 (2 * M) ω ∂μ) * ((2 * M : ℕ) : ℝ≥0∞)⁻¹ := by gcongr
  have hmono : Monotone (fun k : ℕ =>
      ∫⁻ ω, Q.gamma 1 (2 ^ k * N) ω / ((2 ^ k * N : ℕ) : ℝ≥0∞) ∂μ) := by
    refine monotone_nat_of_le_succ fun k => ?_
    have h := key (2 ^ k * N) (Nat.one_le_iff_ne_zero.2 (by positivity))
    simpa only [pow_succ, mul_comm _ 2, mul_assoc] using h
  refine ⟨hmono, ?_⟩
  rw [(tendsto_atTop_iSup hmono).limsup_eq]
  have := le_iSup (fun k : ℕ =>
      ∫⁻ ω, Q.gamma 1 (2 ^ k * N) ω / ((2 ^ k * N : ℕ) : ℝ≥0∞) ∂μ) 0
  simpa using this
