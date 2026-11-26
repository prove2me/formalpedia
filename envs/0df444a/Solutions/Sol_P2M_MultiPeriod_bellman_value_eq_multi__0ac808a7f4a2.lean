-- Prove2me | solution 1 for P2M_MultiPeriod_bellman_value_eq_multi__0ac808a7f4a2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:45.811879+00:00
-- url     : https://prove2.me/submissions/d36e8d13-371e-49fe-b6e6-aecf4f438423

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_FeasNonempty
import Theorems.Thm_P2M_CouplingSet__nonempty_2818265cb747
import Theorems.Thm_P2M_FeasibleSet__nonempty_294b52d3ec45
import Theorems.Thm_MultiPeriod_Feas_nonempty
import Theorems.Thm_MultiPeriod_bellman_value_eq_multi


set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
namespace MultiPeriod
theorem _root_.solution (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀]
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν : ∀ t y, IsProbabilityMeasure (κν t y)) :
    ⨅ (γ₀ : Measure (X 0 × Y 0)) (γ : Strat X Y)
      (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
      (_ : ∀ t h, γ t h ∈ Feas κμ κν t h),
      ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀
    = ⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ :=
  bellman_value_eq_multi κμ κν c T μ₀ ν₀ hκμ (Feas.nonempty κμ κν hκμ hκν)
end MultiPeriod
