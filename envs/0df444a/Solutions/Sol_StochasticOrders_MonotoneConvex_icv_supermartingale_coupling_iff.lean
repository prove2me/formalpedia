-- Prove2me | solution 1 for StochasticOrders.MonotoneConvex.icv_supermartingale_coupling_iff
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T17:01:35.162779+00:00
-- url     : https://prove2.me/submissions/65facbe8-f130-4c78-996b-ad23c9c0223d

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcvOrder

set_option autoImplicit false

open MeasureTheory in
/-- On `Bool` with the trivial σ-algebra `⊥`, the non-constant map `b ↦ if b then 1 else 0` is not
a.e.-measurable for `dirac true`. -/
theorem not_aemeasurable_bot_db259d3f :
    ¬ @AEMeasurable Bool ℝ _ ⊥ (fun b : Bool => if b then (1:ℝ) else 0)
        (@Measure.dirac Bool ⊥ true) := by
  letI : MeasurableSpace Bool := ⊥
  intro h
  obtain ⟨g, hg, hXg⟩ := h
  -- g is constant
  have hconst : ∀ b, g b = g true := by
    have hm : MeasurableSet (g ⁻¹' {g true}) := hg (measurableSet_singleton _)
    rcases MeasurableSpace.measurableSet_bot_iff.mp hm with h0 | h1
    · have : true ∈ g ⁻¹' {g true} := rfl
      rw [h0] at this; exact this.elim
    · intro b
      have : b ∈ g ⁻¹' {g true} := by rw [h1]; trivial
      exact this
  have hnull : (Measure.dirac true) {b : Bool | (if b then (1:ℝ) else 0) ≠ g b} = 0 :=
    ae_iff.mp hXg
  obtain ⟨t, hst, htm, ht0⟩ := exists_measurable_superset_of_null hnull
  rcases MeasurableSpace.measurableSet_bot_iff.mp htm with h0 | h1
  · -- the bad set is empty, so X = g everywhere, but X is non-constant
    have e1 : ∀ b : Bool, (if b then (1:ℝ) else 0) = g b := by
      intro b
      by_contra hb
      have : b ∈ t := hst hb
      rw [h0] at this; exact this
    have := e1 true
    have h2 := e1 false
    rw [hconst false] at h2
    simp at this h2
    linarith
  · rw [h1] at ht0
    simp at ht0

open StochasticOrders.MonotoneConvex MeasureTheory ProbabilityTheory in
theorem solution :
    ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ),
    IcvOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        ρ[Xhat | MeasurableSpace.comap Yhat inferInstance] ≤ᵐ[ρ] Yhat ∧
        (∀ y₁ y₂ : ℝ, y₁ ≤ y₂ → ∀ t : ℝ,
          (condDistrib Xhat Yhat ρ y₁) {x : ℝ | t < x} ≤
            (condDistrib Xhat Yhat ρ y₂) {x : ℝ | t < x})) := by
  intro H
  letI : MeasurableSpace Bool := ⊥
  have hP : IsProbabilityMeasure (Measure.dirac true : Measure Bool) := inferInstance
  have key := (@H Bool Bool ⊥ ⊥ (Measure.dirac true) (Measure.dirac true) hP hP
    (fun b => if b then (1:ℝ) else 0) (fun b => if b then (1:ℝ) else 0)).mp
    (fun φ _ _ _ _ => le_refl _)
  obtain ⟨Ω'', _, ρ, _, Xhat, Yhat, hX, _, _, _⟩ := key
  exact not_aemeasurable_bot_db259d3f hX.aemeasurable_snd
