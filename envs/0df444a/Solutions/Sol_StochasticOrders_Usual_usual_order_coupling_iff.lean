-- Prove2me | solution 1 for StochasticOrders.Usual.usual_order_coupling_iff
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T11:18:23.895193+00:00
-- url     : https://prove2.me/submissions/915947dd-1200-4be1-9b6f-955114778b84

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

/-! Disproof of de32a963 `StochasticOrders.Usual.usual_order_coupling_iff`.

`UsualOrder` puts no measurability condition on `X` or `Y`. `IdentDistrib Xhat X ρ μ` does:
it contains `AEMeasurable X μ`. Take `Ω = Ω'` a two-point type with the trivial σ-algebra
`{∅, univ}`, `μ = ν = ½(δ_hi + δ_lo)`, and `X = Y` with `X hi = 1`, `X lo = 0`.
The left side `UsualOrder μ μ X X` holds by reflexivity. `X` is not a.e.-measurable. The only
measurable sets are `∅` and `univ`, so every measurable `g` is constant. Both points carry mass
`½`, so `X =ᵐ g` forces `X = g` everywhere, but `X` takes two values. So the right side fails. -/

set_option autoImplicit false

open MeasureTheory

/-- A two-point type, given the trivial σ-algebra `{∅, univ}` below. -/
inductive SoUsTwo : Type
  | hi : SoUsTwo
  | lo : SoUsTwo

instance SoUsTwo.instMeasurableSpace : MeasurableSpace SoUsTwo := ⊥

/-- The two-point measure `½(δ_hi + δ_lo)`. -/
noncomputable def soUs_mu : Measure SoUsTwo :=
  (2⁻¹ : ENNReal) • (Measure.dirac SoUsTwo.hi + Measure.dirac SoUsTwo.lo)

/-- The non-measurable random variable `X hi = 1`, `X lo = 0`. -/
def soUs_X : SoUsTwo → ℝ
  | SoUsTwo.hi => 1
  | SoUsTwo.lo => 0

theorem soUs_mu_univ : soUs_mu Set.univ = 1 := by
  rw [soUs_mu, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

instance soUs_mu_prob : IsProbabilityMeasure soUs_mu := ⟨soUs_mu_univ⟩

theorem soUs_mu_pos (b : SoUsTwo) (S : Set SoUsTwo) (hb : b ∈ S) : soUs_mu S ≠ 0 := by
  have key : (2⁻¹ : ENNReal) * Measure.dirac b S ≤ soUs_mu S := by
    rw [soUs_mu, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
    apply mul_le_mul_right
    cases b
    · exact le_self_add
    · exact le_add_self
  rw [Measure.dirac_apply_of_mem hb, mul_one] at key
  intro h
  rw [h] at key
  exact (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top) (le_antisymm key (zero_le))

theorem soUs_not_aemeasurable : ¬ AEMeasurable soUs_X soUs_mu := by
  rintro ⟨g, hg, hXg⟩
  have hall : ∀ b : SoUsTwo, soUs_X b = g b := by
    intro b
    by_contra hne
    exact soUs_mu_pos b {ω | soUs_X ω ≠ g ω} hne (ae_iff.mp hXg)
  have hmeas : MeasurableSet (g ⁻¹' {g SoUsTwo.hi}) := hg (measurableSet_singleton _)
  rcases MeasurableSpace.measurableSet_bot_iff.mp hmeas with h | h
  · have hmem : SoUsTwo.hi ∈ g ⁻¹' {g SoUsTwo.hi} := rfl
    rw [h] at hmem
    exact hmem
  · have hmem : SoUsTwo.lo ∈ g ⁻¹' {g SoUsTwo.hi} := by rw [h]; trivial
    have hft : g SoUsTwo.lo = g SoUsTwo.hi := hmem
    rw [← hall, ← hall] at hft
    norm_num [soUs_X] at hft

open MeasureTheory ProbabilityTheory StochasticOrders.Usual in
theorem solution : ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ),
    UsualOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧ ρ {ω | Xhat ω ≤ Yhat ω} = 1) := by
  intro H
  have hL : UsualOrder soUs_mu soUs_mu soUs_X soUs_X := fun _ => le_rfl
  obtain ⟨Ω'', _, ρ, _, Xhat, Yhat, h1, _, _⟩ :=
    (@H SoUsTwo SoUsTwo SoUsTwo.instMeasurableSpace SoUsTwo.instMeasurableSpace soUs_mu soUs_mu
      soUs_mu_prob soUs_mu_prob soUs_X soUs_X).mp hL
  exact soUs_not_aemeasurable h1.aemeasurable_snd

