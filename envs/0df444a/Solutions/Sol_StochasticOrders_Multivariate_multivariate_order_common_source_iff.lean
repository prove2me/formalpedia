-- Prove2me | solution 1 for StochasticOrders.Multivariate.multivariate_order_common_source_iff
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T10:27:08.343558+00:00
-- url     : https://prove2.me/submissions/56169bf5-fc0b-43b3-8923-5575842df5b4

import Mathlib
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder

/-! Disproof of 947cb63b `StochasticOrders.Multivariate.multivariate_order_common_source_iff`.

`MultivariateOrder` puts no measurability condition on `X` or `Y`. `IdentDistrib (ψ1 ∘ Z) X ρ μ` does:
it contains `AEMeasurable X μ`. Take `n = 1`, `Ω` a two-point type with the trivial σ-algebra `{∅, univ}`,
`μ = ½(δ_hi + δ_lo)`, `X hi = 1`, `X lo = 0`, and `Y ≡ 1` on `Unit` under `δ_()`.
For monotone `φ` with `φ ∘ X` integrable, `∫ φ ∘ X ∂μ ≤ ∫ φ 1 ∂μ = φ 1 = ∫ φ ∘ Y ∂ν`, since
`X ≤ 1` pointwise. So the left side holds. `X` is not a.e.-measurable. The only measurable sets
are `∅` and `univ`, so every measurable `g` is constant. Both points carry mass `½`, so `X =ᵐ g`
forces `X = g` everywhere, but `X` takes two values. So the right side fails. -/

set_option autoImplicit false

open MeasureTheory

/-- A two-point type, given the trivial σ-algebra `{∅, univ}` below. -/
inductive SoMVTwo : Type
  | hi : SoMVTwo
  | lo : SoMVTwo

instance SoMVTwo.instMeasurableSpace : MeasurableSpace SoMVTwo := ⊥

/-- The two-point measure `½(δ_hi + δ_lo)`. -/
noncomputable def soMV_mu : Measure SoMVTwo :=
  (2⁻¹ : ENNReal) • (Measure.dirac SoMVTwo.hi + Measure.dirac SoMVTwo.lo)

/-- The non-measurable vector `X hi = 1`, `X lo = 0`. -/
def soMV_X : SoMVTwo → Fin 1 → ℝ
  | SoMVTwo.hi => fun _ => 1
  | SoMVTwo.lo => fun _ => 0

theorem soMV_mu_univ : soMV_mu Set.univ = 1 := by
  rw [soMV_mu, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

instance soMV_mu_prob : IsProbabilityMeasure soMV_mu := ⟨soMV_mu_univ⟩

theorem soMV_mu_pos (b : SoMVTwo) (S : Set SoMVTwo) (hb : b ∈ S) : soMV_mu S ≠ 0 := by
  have key : (2⁻¹ : ENNReal) * Measure.dirac b S ≤ soMV_mu S := by
    rw [soMV_mu, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
    apply mul_le_mul_right
    cases b
    · exact le_self_add
    · exact le_add_self
  rw [Measure.dirac_apply_of_mem hb, mul_one] at key
  intro h
  rw [h] at key
  exact (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top) (le_antisymm key (zero_le))

theorem soMV_not_aemeasurable : ¬ AEMeasurable soMV_X soMV_mu := by
  rintro ⟨g, hg, hXg⟩
  have hall : ∀ b : SoMVTwo, soMV_X b = g b := by
    intro b
    by_contra hne
    exact soMV_mu_pos b {ω | soMV_X ω ≠ g ω} hne (ae_iff.mp hXg)
  have hmeas : MeasurableSet (g ⁻¹' {g SoMVTwo.hi}) := hg (measurableSet_singleton _)
  rcases MeasurableSpace.measurableSet_bot_iff.mp hmeas with h | h
  · have hmem : SoMVTwo.hi ∈ g ⁻¹' {g SoMVTwo.hi} := rfl
    rw [h] at hmem
    exact hmem
  · have hmem : SoMVTwo.lo ∈ g ⁻¹' {g SoMVTwo.hi} := by rw [h]; trivial
    have hft : g SoMVTwo.lo = g SoMVTwo.hi := hmem
    rw [← hall, ← hall] at hft
    have := congrFun hft 0
    simp [soMV_X] at this

theorem soMV_order_of_le {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {n : ℕ}
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Fin n → ℝ) (c : Fin n → ℝ) (hX : ∀ ω, X ω ≤ c) :
    StochasticOrders.Multivariate.MultivariateOrder μ ν X (fun _ => c) := by
  intro φ hφ hφX _
  calc ∫ ω, φ (X ω) ∂μ ≤ ∫ _, φ c ∂μ :=
        integral_mono hφX (integrable_const _) (fun ω => hφ (hX ω))
    _ = φ c := by simp
    _ = ∫ ω, φ ((fun _ => c) ω) ∂ν := by simp

theorem soMV_X_le (b : SoMVTwo) : soMV_X b ≤ (fun _ => (1 : ℝ)) := by
  intro i
  cases b <;> simp [soMV_X]

open MeasureTheory ProbabilityTheory StochasticOrders.Multivariate in
theorem solution : ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {n : ℕ} (μ : Measure Ω) (ν : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ),
    MultivariateOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Z : Ω'' → ℝ) (ψ1 ψ2 : ℝ → Fin n → ℝ),
        (∀ z : ℝ, ψ1 z ≤ ψ2 z) ∧
        IdentDistrib (ψ1 ∘ Z) X ρ μ ∧ IdentDistrib (ψ2 ∘ Z) Y ρ ν) := by
  intro H
  have hL : MultivariateOrder soMV_mu (Measure.dirac ()) soMV_X (fun _ => fun _ => (1 : ℝ)) :=
    soMV_order_of_le soMV_mu (Measure.dirac ()) soMV_X (fun _ => (1 : ℝ)) soMV_X_le
  obtain ⟨Ω'', _, ρ, _, Z, ψ1, ψ2, _, h1, _⟩ :=
    (@H SoMVTwo Unit SoMVTwo.instMeasurableSpace inferInstance 1 soMV_mu (Measure.dirac ())
      soMV_mu_prob inferInstance soMV_X (fun _ => fun _ => (1 : ℝ))).mp hL
  exact soMV_not_aemeasurable h1.aemeasurable_snd
