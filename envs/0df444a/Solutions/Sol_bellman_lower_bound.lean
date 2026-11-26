-- Prove2me | solution 1 for bellman_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:54.095244+00:00
-- url     : https://prove2.me/submissions/b5792eeb-c9fa-4772-824f-b9c373a7c4af

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_LowerBound
import Theorems.Thm_P2M_V__le_cost_pointwise_ab482f27815a

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
theorem _root_.solution
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁)))
    (kd : KernelDecomp π)
    (h_feas : ∀ᵐ z₀ ∂kd.γ₀, kd.γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀) :
    ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂kd.γ₀
    ≤ totalCost c₀ c₁ kd.γ₀ kd.γ₁ := by
  unfold totalCost; apply lintegral_mono_ae
  filter_upwards [h_feas] with z₀ hz₀
  exact V₀_le_cost_pointwise c₀ c₁ κ_μ κ_ν z₀ (kd.γ₁ z₀) hz₀
