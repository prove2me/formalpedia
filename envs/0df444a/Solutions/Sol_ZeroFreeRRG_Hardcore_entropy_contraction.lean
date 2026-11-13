-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.entropy_contraction
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:31:47.0642+00:00
-- url     : https://prove2.me/submissions/a74d4e97-1d3b-497e-bd6b-25c4558c8ec6

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open ZeroFreeRRG.Hardcore

/-- The pointwise entropy contraction used in the Potts comparison. -/
theorem xlogx_affine_le (x c : ℝ) (hx : 0 ≤ x) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    xlogx (1-c+c*x) ≤ c*xlogx x := by
  have h := Real.convexOn_mul_log.2 (show (1:ℝ) ∈ Set.Ici 0 by norm_num)
    (show x ∈ Set.Ici 0 from hx) (show 0 ≤ 1-c by linarith) hc0 (by ring : 1-c+c=1)
  simpa [xlogx, smul_eq_mul, Real.log_one] using h

/-- Strictness holds away from the constant edge factor. -/
theorem xlogx_affine_lt (x c : ℝ) (hx : 0 ≤ x) (hc0 : 0 < c) (hc1 : c < 1)
    (hne : x ≠ 1) : xlogx (1-c+c*x) < c*xlogx x := by
  have h := Real.strictConvexOn_mul_log.2 (show (1:ℝ) ∈ Set.Ici 0 by norm_num)
    (show x ∈ Set.Ici 0 from hx) (Ne.symm hne) (show 0 < 1-c by linarith) hc0 (by ring : 1-c+c=1)
  simpa [xlogx, smul_eq_mul, Real.log_one] using h

open MeasureTheory

/-- Integrating the contraction gives the entropy comparison, with strictness for a nonconstant factor. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (E : Ω → ℝ)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hE : ∀ᵐ ω ∂μ, 0 ≤ E ω)
    (hI : Integrable (fun ω => xlogx (E ω)) μ)
    (hJ : Integrable (fun ω => xlogx (1-c+c*E ω)) μ) :
    (∫ ω, xlogx (1-c+c*E ω) ∂μ) ≤ c * ∫ ω, xlogx (E ω) ∂μ ∧
      (0 < μ {ω | 0 ≤ E ω ∧ E ω ≠ 1} →
        (∫ ω, xlogx (1-c+c*E ω) ∂μ) < c * ∫ ω, xlogx (E ω) ∂μ) := by
  have hle : ∀ᵐ ω ∂μ, xlogx (1-c+c*E ω) ≤ c*xlogx (E ω) := by
    filter_upwards [hE] with ω hω
    exact xlogx_affine_le (E ω) c hω hc0.le hc1.le
  constructor
  · have h := integral_mono_ae hJ (hI.const_mul c) hle
    simpa only [integral_const_mul] using h
  · intro hpositive
    let gap : Ω → ℝ := fun ω => c*xlogx (E ω) - xlogx (1-c+c*E ω)
    have hgap : Integrable gap μ := (hI.const_mul c).sub hJ
    have hnonneg : 0 ≤ᵐ[μ] gap := by
      filter_upwards [hle] with ω hω
      exact sub_nonneg.mpr hω
    have hs : {ω | 0 ≤ E ω ∧ E ω ≠ 1} ⊆ Function.support gap := by
      intro ω hω
      change gap ω ≠ 0
      dsimp [gap]
      have h := xlogx_affine_lt (E ω) c hω.1 hc0 hc1 hω.2
      linarith
    have hspos : 0 < μ (Function.support gap) := lt_of_lt_of_le hpositive (measure_mono hs)
    have hp := (integral_pos_iff_support_of_nonneg_ae hnonneg hgap).2 hspos
    dsimp [gap] at hp
    rw [integral_sub (hI.const_mul c) hJ, integral_const_mul] at hp
    linarith
