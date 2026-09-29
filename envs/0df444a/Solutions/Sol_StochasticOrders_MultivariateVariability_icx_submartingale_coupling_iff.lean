-- Prove2me | solution 1 for StochasticOrders.MultivariateVariability.icx_submartingale_coupling_iff
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T18:20:51.235196+00:00
-- url     : https://prove2.me/submissions/a7c5c5ab-b81a-4c1d-aaf0-c6fb3ed3d37f

import Mathlib
import Definitions.Def_StochasticOrders_MultivariateVariability_IcxOrder

/-! Disproof of 5b1ab376
`StochasticOrders.MultivariateVariability.icx_submartingale_coupling_iff`.

The statement puts no integrability hypothesis on `X` or `Y`. Mathlib's conditional
expectation of a non-integrable function is `0`. So the right-hand side forces `X̂ ≤ 0` a.s.
whenever `Y` is not integrable. The left-hand side `X ≤icx X` always holds.

Take `n = 1`, `Ω = Ω' = ℝ`, `μ = ν = volume` restricted to `(0, 1]` (a probability measure),
and `X = Y = x ↦ (fun _ => x⁻¹)`, whose single coordinate `x⁻¹` is positive on `(0, 1]` and
not integrable there. Then `IcxOrder μ μ X X` holds by reflexivity. Suppose a coupling
`(X̂, Ŷ)` on `(Ω'', ρ)` exists. Since `Ŷ =st Y` and `Y` is not integrable, `Ŷ` is not
integrable, so `ρ[Ŷ | σ(X̂)] = 0`. The submartingale condition then gives `X̂ ≤ 0` a.s.
Since `X̂ =st X`, also `X ≤ 0` `μ`-a.s. But `X > 0` on `(0, 1]`, which has full `μ`-measure:
contradiction. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open StochasticOrders.MultivariateVariability in
theorem solution : ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {n : ℕ} (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ),
    IcxOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → Fin n → ℝ),
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        Xhat ≤ᵐ[ρ] ρ[Yhat | MeasurableSpace.comap Xhat inferInstance]) := by
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
  have hco : IcxOrder (volume.restrict (Set.Ioc (0 : ℝ) 1))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) (fun x : ℝ => fun _ : Fin 1 => x⁻¹)
      (fun x : ℝ => fun _ : Fin 1 => x⁻¹) :=
    fun _ _ _ _ _ => le_rfl
  obtain ⟨Ω'', m'', ρ, hρ, Xh, Yh, hX, hY, hce⟩ :=
    (hT (volume.restrict (Set.Ioc (0 : ℝ) 1)) (volume.restrict (Set.Ioc (0 : ℝ) 1))
      (fun x : ℝ => fun _ : Fin 1 => x⁻¹) (fun x : ℝ => fun _ : Fin 1 => x⁻¹)).1 hco
  have hYni : ¬ Integrable Yh ρ := fun h => hni (hY.integrable_iff.1 h)
  rw [condExp_of_not_integrable hYni] at hce
  have hXh : ∀ᵐ ω ∂ρ, Xh ω ≤ 0 := hce
  have hmeas : MeasurableSet {v : Fin 1 → ℝ | v ≤ 0} :=
    (isClosed_le continuous_id continuous_const).measurableSet
  have hXle : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      (fun _ : Fin 1 => x⁻¹) ≤ 0 :=
    hX.ae_snd (p := fun v : Fin 1 → ℝ => v ≤ 0) hmeas hXh
  have hmem : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), x ∈ Set.Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  obtain ⟨x, hxle, hx⟩ := (hXle.and hmem).exists
  have h0 : x⁻¹ ≤ 0 := hxle 0
  exact absurd h0 (not_le.2 (inv_pos.2 hx.1))
