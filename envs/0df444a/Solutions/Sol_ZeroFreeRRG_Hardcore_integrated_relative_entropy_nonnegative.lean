-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.integrated_relative_entropy_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:40:33.953443+00:00
-- url     : https://prove2.me/submissions/2b3941eb-8f27-4a97-87b1-9c79ee69fe12

import Mathlib
set_option autoImplicit false

/-- The pointwise relative-entropy gap is nonnegative. -/
private theorem pointwise_gap (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    0 ≤ p * Real.log p - p * Real.log q - p + q := by
  by_cases hp0 : p = 0
  · simp [hp0, le_of_lt hq]
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have hdiv : 0 ≤ p/q := div_nonneg hp hq.le
    have hbase := Real.self_sub_one_le_mul_log hdiv
    have hh := mul_le_mul_of_nonneg_left hbase hq.le
    rw [Real.log_div hp0 (ne_of_gt hq)] at hh
    have hqn : q ≠ 0 := ne_of_gt hq
    have hc : q * (p/q) = p := by field_simp
    nlinarith [hh]

open MeasureTheory


theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (p q : Ω → ℝ)
    (hpos : ∀ᵐ ω ∂μ, 0 ≤ p ω ∧ 0 ≤ q ω ∧ (q ω = 0 → p ω = 0))
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hpp : Integrable (fun ω => p ω * Real.log (p ω)) μ)
    (hpq : Integrable (fun ω => p ω * Real.log (q ω)) μ)
    (hmass : (∫ ω, p ω ∂μ) = ∫ ω, q ω ∂μ) :
    (∫ ω, p ω * Real.log (q ω) ∂μ) ≤ ∫ ω, p ω * Real.log (p ω) ∂μ := by
  have hgap : 0 ≤ᵐ[μ] (fun ω => p ω * Real.log (p ω) - p ω * Real.log (q ω) - p ω + q ω) := by
    filter_upwards [hpos] with ω hω
    by_cases hq0 : q ω = 0
    · have hp0 := hω.2.2 hq0
      simp [hp0,hq0]
    · exact pointwise_gap (p ω) (q ω) hω.1 (lt_of_le_of_ne hω.2.1 (Ne.symm hq0))
  have hi := integral_nonneg_of_ae hgap
  have heq : (∫ ω, p ω * Real.log (p ω) - p ω * Real.log (q ω) - p ω + q ω ∂μ) =
      (∫ ω, p ω * Real.log (p ω) ∂μ) - (∫ ω, p ω * Real.log (q ω) ∂μ) -
      (∫ ω, p ω ∂μ) + (∫ ω, q ω ∂μ) := by
    have h1 := integral_add ((hpp.sub hpq).sub hp) hq
    have h2 := integral_sub (hpp.sub hpq) hp
    have h3 := integral_sub hpp hpq
    simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
    rw [h1,h2,h3]
  rw [heq,hmass] at hi
  linarith
