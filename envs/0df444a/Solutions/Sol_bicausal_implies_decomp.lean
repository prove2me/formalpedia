-- Prove2me | solution 1 for bicausal_implies_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:46.412739+00:00
-- url     : https://prove2.me/submissions/0b1fa96e-626f-4694-929c-811811719847

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_Proposition1

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
theorem _root_.solution
    (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁)))
    (hbc : IsBicausal₂ μ₀ ν₀ κ_μ κ_ν π) :
    ∃ (kd : KernelDecomp π),
      kd.γ₀ ∈ CouplingSet₀ μ₀ ν₀ ∧
      ∀ᵐ z₀ ∂kd.γ₀, kd.γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀ := by
  obtain ⟨kd, h_coupling, h_feas⟩ := hbc
  exact ⟨kd, h_coupling, h_feas⟩
