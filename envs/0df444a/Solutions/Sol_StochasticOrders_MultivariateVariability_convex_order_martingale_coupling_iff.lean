-- Prove2me | solution 1 for StochasticOrders.MultivariateVariability.convex_order_martingale_coupling_iff
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T18:03:59.257628+00:00
-- url     : https://prove2.me/submissions/eb0998e2-97af-4ddc-910a-4bf0bfcd3e29

import Mathlib
import Definitions.Def_StochasticOrders_MultivariateVariability_ConvexOrder

/-! Disproof of 9d9f894d
`StochasticOrders.MultivariateVariability.convex_order_martingale_coupling_iff`.

The statement puts no integrability hypothesis on `X` or `Y`. Mathlib's conditional
expectation of a non-integrable function is `0`. So the right-hand side forces `X̂` to be
integrable whenever `Y` is not, which is impossible when `X` has the same law as a
non-integrable `Y`. The left-hand side `X ≤cx X` always holds.

Take `n = 1`, `Ω = Ω' = ℝ`, `μ = ν = volume` restricted to `(0, 1]` (a probability measure),
and `X = Y = x ↦ (fun _ => x⁻¹)`, whose single coordinate `x⁻¹` is not integrable on `(0, 1]`.
Then `ConvexOrder μ μ X X` holds by reflexivity. Suppose a coupling `(X̂, Ŷ)` on `(Ω'', ρ)`
exists. Since `Ŷ =st Y` and `Y` is not integrable, `Ŷ` is not integrable, so
`ρ[Ŷ | σ(X̂)] = 0`. The martingale condition then gives `X̂ =ᵐ 0`, so `X̂` is integrable.
Since `X̂ =st X`, `X` would be integrable: contradiction. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open StochasticOrders.MultivariateVariability in
theorem solution : ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ),
    ConvexOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → Fin n → ℝ),
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] =ᵐ[ρ] Xhat) := by
  intro hT
  have hP : IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  have hni0 : ¬ Integrable (fun x : ℝ => x⁻¹) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro h
    have hii : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 h
    rw [intervalIntegrable_inv_iff] at hii
    simp at hii
  have hni : ¬ Integrable (fun x : ℝ => fun _ : Fin 1 => x⁻¹)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun h => hni0 (h.eval 0)
  have hco : ConvexOrder (volume.restrict (Set.Ioc (0 : ℝ) 1))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) (fun x : ℝ => fun _ : Fin 1 => x⁻¹)
      (fun x : ℝ => fun _ : Fin 1 => x⁻¹) :=
    fun _ _ _ _ => le_rfl
  obtain ⟨Ω'', m'', ρ, hρ, Xh, Yh, hX, hY, hce⟩ :=
    (hT (volume.restrict (Set.Ioc (0 : ℝ) 1)) (volume.restrict (Set.Ioc (0 : ℝ) 1))
      (fun x : ℝ => fun _ : Fin 1 => x⁻¹) (fun x : ℝ => fun _ : Fin 1 => x⁻¹)).1 hco
  have hYni : ¬ Integrable Yh ρ := fun h => hni (hY.integrable_iff.1 h)
  rw [condExp_of_not_integrable hYni] at hce
  have hXi : Integrable Xh ρ := (integrable_zero Ω'' (Fin 1 → ℝ) ρ).congr hce
  exact hni (hX.integrable_iff.1 hXi)
