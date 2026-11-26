-- Prove2me | solution 1 for P2M_totalCost_le_V__plus_eps_6896a197c034
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:35.731983+00:00
-- url     : https://prove2.me/submissions/bc03c900-4cfe-4690-ab9d-903b492ed818

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_DescriptiveSetTheory_JankovVonNeumann
import Definitions.Def_BicausalOT_UpperBound

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
theorem _root_.solution
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (γ₀ : Measure (X₀ × Y₀))
    (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
    (ε : ENNReal)
    (h_opt : ∀ z₀, ∫⁻ z₁, c₁ (z₀, z₁) ∂(γ₁ z₀)
      ≤ (⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
          ∫⁻ z₁, c₁ (z₀, z₁) ∂m) + ε) :
    totalCost c₀ c₁ γ₀ γ₁
    ≤ ∫⁻ z₀, (V₀ c₀ c₁ κ_μ κ_ν z₀ + ε) ∂γ₀ := by
  unfold totalCost; apply lintegral_mono; intro z₀
  show c₀ z₀ + ∫⁻ z₁, c₁ (z₀, z₁) ∂(γ₁ z₀) ≤ V₀ c₀ c₁ κ_μ κ_ν z₀ + ε
  have h := h_opt z₀
  have hV : V₀ c₀ c₁ κ_μ κ_ν z₀ = c₀ z₀ +
    ⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
      ∫⁻ z₁, c₁ (z₀, z₁) ∂m := rfl
  rw [hV]
  calc c₀ z₀ + ∫⁻ z₁, c₁ (z₀, z₁) ∂(γ₁ z₀)
      ≤ c₀ z₀ + ((⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
          ∫⁻ z₁, c₁ (z₀, z₁) ∂m) + ε) := by gcongr
    _ = c₀ z₀ + (⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
          ∫⁻ z₁, c₁ (z₀, z₁) ∂m) + ε := by rw [← add_assoc]
