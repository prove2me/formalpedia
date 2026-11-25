-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.sqrt_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:52.967224+00:00
-- url     : https://prove2.me/submissions/4e36f638-5545-4fd3-9092-4bee007effc8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MinimumGrowthBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer TwoSidedBoostBounds
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds
theorem _root_.solution (A : ℝ) {k1 k2 L Ly : ℝ} (hk1 : 0 < k1) (hk12 : k1 ≤ k2) (hL : 0 ≤ L)
    (h1 : k1 * L ≤ Ly) (h2 : Ly ≤ k2 * L) :
    Real.sqrt Ly ^ (-A) ≤ max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * Real.sqrt L ^ (-A) := by
  rcases hL.eq_or_lt with hL0 | hLpos
  · subst hL0
    have hLy : Ly = 0 := le_antisymm (by linarith) (by linarith)
    subst hLy
    simp only [Real.sqrt_zero]
    by_cases hA : A = 0
    · subst hA
      simp
    · rw [Real.zero_rpow (neg_ne_zero.mpr hA), mul_zero]
  · have hs : ∀ z : ℝ, 0 ≤ z → Real.sqrt z ^ (-A) = z ^ (-A / 2) := by
      intro z hz
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz]
      congr 1
      ring
    have hLy : 0 < Ly := lt_of_lt_of_le (mul_pos hk1 hLpos) h1
    rw [hs Ly hLy.le, hs L hL]
    have hLy_eq : Ly = Ly / L * L := (div_mul_cancel₀ Ly hLpos.ne').symm
    have hs1 : k1 ≤ Ly / L := by
      rw [le_div_iff₀ hLpos]
      exact h1
    have hs2 : Ly / L ≤ k2 := by
      rw [div_le_iff₀ hLpos]
      exact h2
    have hspos : 0 < Ly / L := lt_of_lt_of_le hk1 hs1
    rw [hLy_eq, Real.mul_rpow hspos.le hL]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL _)
    rcases le_total 0 (-A / 2) with hp | hp
    · exact (Real.rpow_le_rpow hspos.le hs2 hp).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hk1 hs1 hp).trans (le_max_left _ _)
end ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds
