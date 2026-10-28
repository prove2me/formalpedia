-- Prove2me | solution 1 for avram_ws01e_a_finite_grid_ae_stop_cylinder_membership_9136b6b1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:10:36.117599+00:00
-- url     : https://prove2.me/submissions/787e0e4d-7bfe-4dc5-badf-7edb5403d6ca

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T u : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ᵐ ω ∂(P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))), τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s + u ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ s ∈ grid,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B) 
    (hfib : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s}))
    (hXm : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); ∀ r, Measurable (X.X r)))
    (hinc : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); ∀ s, MeasurableSet ((fun ω => X.X (s + u) ω -
      X.X s ω) ⁻¹' B)))
    (hAae : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); ∀ᵐ ω ∂QT,
      (ω ∈ A ↔ ω ∈ ⋃ s ∈ grid, C s)))
    : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); ∀ᵐ ω ∂QT,
      (ω ∈ A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} ↔
       ω ∈ ⋃ s ∈ grid, D s)) := by
    let QT : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}
    let D : ℝ≥0 → Set Ω := fun s =>
        C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B
    filter_upwards [hgrid] with ω hω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_preimage, exists_prop, D, C]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨τ ω, hω, ⟨ha, rfl⟩, hb⟩
    · rintro ⟨s, -, ⟨ha, rfl⟩, hb⟩
      exact ⟨ha, hb⟩
