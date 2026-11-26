-- Prove2me | solution 1 for bellman_value_leq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:00:53.258187+00:00
-- url     : https://prove2.me/submissions/e27ada3d-4141-4cd1-a150-ea2e3d4f414f

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
    (μ₀ : Measure X₀) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure Y₀) [IsProbabilityMeasure ν₀]
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (h_Gamma_ne : ∀ z₀, (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty)
    (h_prob : ∀ γ₀ ∈ CouplingSet₀ μ₀ ν₀, γ₀ Set.univ ≤ 1) :
    ⨅ (γ₀ : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀ γ₁
    ≤ ⨅ (γ₀ : Measure (X₀ × Y₀)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
        ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ := by
  apply le_iInf; intro γ₀; apply le_iInf; intro h_coup
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨γ₁_sel, hγ₁_feas, hγ₁_opt⟩ :=
    eps_optimal_kernel_bound c₁ κ_μ κ_ν h_Gamma_ne ε (by positivity)
  calc ⨅ (γ₀' : Measure (X₀ × Y₀)) (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁))
        (_ : γ₀' ∈ CouplingSet₀ μ₀ ν₀)
        (_ : ∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀),
        totalCost c₀ c₁ γ₀' γ₁
      ≤ totalCost c₀ c₁ γ₀ γ₁_sel := by
        apply iInf_le_of_le γ₀; apply iInf_le_of_le γ₁_sel
        apply iInf_le_of_le h_coup; exact iInf_le _ hγ₁_feas
    _ ≤ ∫⁻ z₀, (V₀ c₀ c₁ κ_μ κ_ν z₀ + ↑ε) ∂γ₀ :=
        totalCost_le_V₀_plus_eps c₀ c₁ κ_μ κ_ν γ₀ γ₁_sel ↑ε hγ₁_opt
    _ = ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ + ↑ε * γ₀ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ ∫⁻ z₀, V₀ c₀ c₁ κ_μ κ_ν z₀ ∂γ₀ + ↑ε := by
        gcongr
        calc ↑ε * γ₀ Set.univ ≤ ↑ε * 1 := by
              gcongr; exact h_prob γ₀ h_coup
          _ = ↑ε := mul_one _
