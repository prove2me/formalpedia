-- Prove2me | solution 1 for StochasticOrders.Convex.convex_order_martingale_coupling_iff
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T17:44:44.600985+00:00
-- url     : https://prove2.me/submissions/63580790-83c6-4255-a4f9-2f9dc0cb6385

import Mathlib
import Definitions.Def_StochasticOrders_Convex_ConvexOrder

/-! Disproof of be018da9 `StochasticOrders.Convex.convex_order_martingale_coupling_iff`.

The statement puts no integrability hypothesis on `X` or `Y`. Mathlib's conditional
expectation of a non-integrable function is `0`. So the right-hand side forces `X̂` to be
integrable whenever `Y` is not, which is impossible when `X` has the same law as a
non-integrable `Y`. The left-hand side `X ≤cx X` always holds.

Take `Ω = Ω' = ℝ`, `μ = ν = volume` restricted to `(0, 1]` (a probability measure), and
`X = Y = x ↦ x⁻¹`, which is not integrable on `(0, 1]`. Then `ConvexOrder μ μ X X` holds by
reflexivity. Suppose a coupling `(X̂, Ŷ)` on `(Ω'', ρ)` exists. Since `Ŷ =st Y` and `Y` is not
integrable, `Ŷ` is not integrable, so `ρ[Ŷ | σ(X̂)] = 0`. The martingale condition then gives
`X̂ =ᵐ 0`, so `X̂` is integrable. Since `X̂ =st X`, `X` would be integrable: contradiction. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open StochasticOrders.Convex in
theorem solution : ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ),
    ConvexOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] =ᵐ[ρ] Xhat ∧
        (∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ,
          (condDistrib Yhat Xhat ρ x₁) {y : ℝ | t < y} ≤
            (condDistrib Yhat Xhat ρ x₂) {y : ℝ | t < y})) := by
  intro hT
  have hP : IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  have hni : ¬ Integrable (fun x : ℝ => x⁻¹) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro h
    have hii : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 h
    rw [intervalIntegrable_inv_iff] at hii
    simp at hii
  have hco : ConvexOrder (volume.restrict (Set.Ioc (0 : ℝ) 1))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) (fun x : ℝ => x⁻¹) (fun x : ℝ => x⁻¹) :=
    fun _ _ _ _ => le_rfl
  obtain ⟨Ω'', m'', ρ, hρ, Xh, Yh, hX, hY, hce, -⟩ :=
    (hT (volume.restrict (Set.Ioc (0 : ℝ) 1)) (volume.restrict (Set.Ioc (0 : ℝ) 1))
      (fun x : ℝ => x⁻¹) (fun x : ℝ => x⁻¹)).1 hco
  have hYni : ¬ Integrable Yh ρ := fun h => hni (hY.integrable_iff.1 h)
  rw [condExp_of_not_integrable hYni] at hce
  have hXi : Integrable Xh ρ := (integrable_zero Ω'' ℝ ρ).congr hce
  exact hni (hX.integrable_iff.1 hXi)

