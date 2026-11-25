-- Prove2me | solution 1 for PI.FdFjNearSup.W.ab_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:52.245848+00:00
-- url     : https://prove2.me/submissions/16ce17c7-7737-41ee-bd7d-7c42ccb95f2d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FdFjNearSup PI.FdFjNearSup.W
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace PI.FdFjNearSup.W
theorem _root_.solution {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1 / 36) :
    0 < (1 - ρ) / (1 + ρ) ∧ ((1 - ρ) / (1 + ρ))⁻¹ = (1 + ρ) / (1 - ρ) ∧
      1 - 2 * ρ ≤ (1 - ρ) / (1 + ρ) ∧ (1 + ρ) / (1 - ρ) ≤ 1 + 3 * ρ ∧ 1 ≤ (1 + ρ) / (1 - ρ) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have h2ρ : 0 < 1 + ρ := by linarith
  refine ⟨div_pos h1ρ h2ρ, inv_div _ _, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ h2ρ]
    nlinarith
  · rw [div_le_iff₀ h1ρ]
    nlinarith
  · rw [le_div_iff₀ h1ρ]
    linarith
end PI.FdFjNearSup.W
