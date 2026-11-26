-- Prove2me | solution 1 for bellman_value_geq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:00:00.98149+00:00
-- url     : https://prove2.me/submissions/4fe52b60-0672-466c-bc83-a004ebc121be

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_LowerBound
import Definitions.Def_BicausalOT_UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_BicausalOT_ValueRepresentation
import Theorems.Thm_P2M_V__le_cost_pointwise_ab482f27815a


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
theorem _root_.solution
    (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁) :
    ⨅ (γ₀ : Measure (X₀ × Y₀)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀
    ≤ ⨅ (γ₀ : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀ γ₁ := by
  apply le_iInf; intro γ₀; apply le_iInf; intro γ₁
  apply le_iInf; intro h_coup; apply le_iInf; intro h_feas
  calc ⨅ (γ₀' : Measure (X₀ × Y₀)) (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀),
        ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀'
      ≤ ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ := iInf₂_le γ₀ h_coup
    _ ≤ totalCost c₀ c₁ γ₀ γ₁ := by
        unfold totalCost; apply lintegral_mono; intro z₀
        exact V₀_le_cost_pointwise c₀ c₁ κ_μ κ_ν z₀ (γ₁ z₀) (h_feas z₀)
