-- Prove2me | solution 1 for bellman_value_leq_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:00:54.625894+00:00
-- url     : https://prove2.me/submissions/86631d40-e3e5-4bc4-b30f-5a0d40da3208

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_LowerBound
import Definitions.Def_BicausalOT_UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_BicausalOT_ValueRepresentation
import Theorems.Thm_P2M_totalCost_le_V__plus_eps_6896a197c034
import Theorems.Thm_eps_optimal_kernel_bound


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
theorem _root_.solution
    {μ₀ : Measure X₀} {ν₀ : Measure Y₀}
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (h_Gamma_ne : ∀ z₀, (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty)
    (γ₀ : Measure (X₀ × Y₀))
    (h_coup : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
    (ε : ENNReal) (hε : 0 < ε) :
    ⨅ (γ₀' : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀' γ₁
    ≤ ∫⁻ z₀, (V₀ c₀ c₁ κ_μ κ_ν z₀ + ε) ∂γ₀ := by
  obtain ⟨γ₁_sel, hγ₁_feas, hγ₁_opt⟩ :=
    eps_optimal_kernel_bound c₁ κ_μ κ_ν h_Gamma_ne ε hε
  calc ⨅ (γ₀' : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀' γ₁
      ≤ totalCost c₀ c₁ γ₀ γ₁_sel := by
        apply iInf_le_of_le γ₀; apply iInf_le_of_le γ₁_sel
        apply iInf_le_of_le h_coup; exact iInf_le _ hγ₁_feas
    _ ≤ ∫⁻ z₀, (V₀ c₀ c₁ κ_μ κ_ν z₀ + ε) ∂γ₀ :=
        totalCost_le_V₀_plus_eps c₀ c₁ κ_μ κ_ν γ₀ γ₁_sel ε hγ₁_opt
