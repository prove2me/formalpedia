-- Prove2me | solution 1 for P2M_bellman_value_eq__629ebbd0a78b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:29.272624+00:00
-- url     : https://prove2.me/submissions/8452234e-19ee-46ed-ad9c-db2dbbeb9360

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_FeasNonempty
import Theorems.Thm_P2M_CouplingSet__nonempty_2818265cb747
import Theorems.Thm_P2M_FeasibleSet__nonempty_294b52d3ec45
import Theorems.Thm_P2M_CouplingSet__measure_univ_db95189062ba
import Theorems.Thm_MultiPeriod_Feas_measure_univ
import Theorems.Thm_bellman_value_eq


set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
theorem _root_.solution
    (μ₀ : Measure X₀) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure Y₀) [IsProbabilityMeasure ν₀]
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (hκμ : ∀ x, IsProbabilityMeasure (κ_μ x))
    (hκν : ∀ y, IsProbabilityMeasure (κ_ν y)) :
    ⨅ (γ₀ : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀ γ₁
    = ⨅ (γ₀ : Measure (X₀ × Y₀)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
        ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ :=
  bellman_value_eq c₀ c₁ μ₀ ν₀ κ_μ κ_ν
    (FeasibleSet₀.nonempty κ_μ κ_ν hκμ hκν)
    (fun _ hγ₀ => le_of_eq (CouplingSet₀.measure_univ hγ₀))
