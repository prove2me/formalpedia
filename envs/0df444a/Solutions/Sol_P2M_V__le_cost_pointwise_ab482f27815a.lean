-- Prove2me | solution 1 for P2M_V__le_cost_pointwise_ab482f27815a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:15.647261+00:00
-- url     : https://prove2.me/submissions/48667dfe-0bc8-4f68-a187-02af277c3826

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_LowerBound

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
set_option linter.unusedSectionVars false
theorem _root_.solution
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (z₀ : X₀ × Y₀) (γ : Measure (X₁ × Y₁))
    (hγ : γ ∈ FeasibleSet₀ κ_μ κ_ν z₀) :
    V₀ c₀ c₁ κ_μ κ_ν z₀ ≤ c₀ z₀ + ∫⁻ z₁, c₁ (z₀, z₁) ∂γ := by
  unfold V₀; gcongr; exact iInf₂_le γ hγ
