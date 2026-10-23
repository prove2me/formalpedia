-- Prove2me | solution 1 for OpaquePricing.Dominance.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T05:58:58.068704+00:00
-- url     : https://prove2.me/submissions/6618cc98-73a1-4770-9c04-2946bd5316e5

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Theorems.Thm_OpaquePricing_Dominance_case_i
import Theorems.Thm_OpaquePricing_Dominance_case_ii

open MeasureTheory
open OpaquePricing.Dominance

theorem solution {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ0 : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (hexch : Exchangeable μ)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcase : α = 1 ∨ TwoValued μ) :
    optDP μ ≤ optOPQ μ α := by
  rcases hcase with rfl | htwo
  · exact case_i hN μ hμ0 hexch
  · exact case_ii hN μ hμ0 hexch htwo α hα0 hα1
