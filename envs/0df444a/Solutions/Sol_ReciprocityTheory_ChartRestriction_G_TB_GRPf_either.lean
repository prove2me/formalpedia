-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GRPf.either
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:11.86136+00:00
-- url     : https://prove2.me/submissions/57c55e9b-bb23-4b62-8801-1057c90a7eff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GRPf
variable {O k : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k]
variable {T : Type} (χ : T → O →+* k) (cc : T → T) (hcc : ∀ σ a, χ (cc σ) a = χ σ (star a))
  (hunit : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a))
include hunit
namespace ReciprocityTheory.ChartRestriction.G.TB.GRPf
theorem _root_.solution {c : k} (hc : c ≠ 0) (σ τ₁ τ₂ : T)
    (P : ∀ a, c * ((χ σ a - χ τ₁ a) * (χ σ a - χ τ₂ a)) = 0) : σ = τ₁ ∨ σ = τ₂ := by
  by_contra hne
  push_neg at hne
  obtain ⟨a₁, hu₁⟩ := hunit σ τ₁ hne.1
  obtain ⟨a₂, hu₂⟩ := hunit σ τ₂ hne.2
  have e1 : c * (χ σ a₁ - χ τ₂ a₁) = 0 := by
    have h' : (χ σ a₁ - χ τ₁ a₁) * (c * (χ σ a₁ - χ τ₂ a₁)) = 0 := by linear_combination P a₁
    exact hu₁.mul_right_eq_zero.1 h'
  have e2 : c * (χ σ a₂ - χ τ₁ a₂) = 0 := by
    have h' : (χ σ a₂ - χ τ₂ a₂) * (c * (χ σ a₂ - χ τ₁ a₂)) = 0 := by linear_combination P a₂
    exact hu₂.mul_right_eq_zero.1 h'
  have e3 := P (a₁ + a₂)
  simp only [map_add] at e3
  have e4 : ((χ σ a₁ - χ τ₁ a₁) * (χ σ a₂ - χ τ₂ a₂)) * c = 0 := by
    linear_combination e3 - ((χ σ a₁ - χ τ₁ a₁) + (χ σ a₂ - χ τ₁ a₂)) * e1 - (χ σ a₂ - χ τ₂ a₂) * e2
  exact hc ((hu₁.mul hu₂).mul_right_eq_zero.1 e4)
end ReciprocityTheory.ChartRestriction.G.TB.GRPf
