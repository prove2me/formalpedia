-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:41.505742+00:00
-- url     : https://prove2.me/submissions/5aa39ee0-a1c8-4d4b-9396-03fb8aaaca52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MinimumGrowthBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MinimumGrowthBounds_minimumSq_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MinimumGrowthBounds_minimumSq_two_sided_bounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MinimumGrowthBounds_sqrt_rpow_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MinimumGrowthBounds_nfac_pos

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
theorem _root_.solution (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ)
    (hmod : ∀ z ∈ X.dom, X.pnorm la P z ≤ C * X.la1 z ^ (-A)) {x y : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hy : y ∈ X.dom) {k1 k2 : ℝ} (hk1 : 0 < k1) (hk12 : k1 ≤ k2)
    (hlow : ∀ τ w, k1 * X.maj x τ w ≤ X.maj y τ w) (hup : ∀ τ w, X.maj y τ w ≤ k2 * X.maj x τ w)
    {R : ℝ} (hR : X.nfac la x / X.nfac la y ≤ R) :
    ‖P y‖ * X.nfac la x ≤ max C 0 * max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * R * X.la1 x ^ (-A) := by
  have hny := nfac_pos X la hy
  have hnx := nfac_pos X la hx
  obtain ⟨b1, b2⟩ := minimumSq_two_sided_bounds X hx hy hk1.le (lt_of_lt_of_le hk1 hk12) hlow hup
  have hla : X.la1 y ^ (-A) ≤ max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * X.la1 x ^ (-A) :=
    sqrt_rpow_le A hk1 hk12 (minimumSq_nonneg X hx) b1 b2
  have hq0 : 0 ≤ X.nfac la x / X.nfac la y := div_nonneg hnx.le hny.le
  have hR0 : 0 ≤ R := le_trans hq0 hR
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hly : 0 ≤ X.la1 y ^ (-A) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hPy : ‖P y‖ * X.nfac la y ≤ max C 0 * X.la1 y ^ (-A) :=
    calc ‖P y‖ * X.nfac la y = X.pnorm la P y := rfl
      _ ≤ C * X.la1 y ^ (-A) := hmod y hy
      _ ≤ max C 0 * X.la1 y ^ (-A) := mul_le_mul_of_nonneg_right (le_max_left _ _) hly
  have hny' := hny.ne'
  calc ‖P y‖ * X.nfac la x = (‖P y‖ * X.nfac la y) * (X.nfac la x / X.nfac la y) := by
        field_simp
    _ ≤ (max C 0 * X.la1 y ^ (-A)) * R := mul_le_mul hPy hR hq0 (mul_nonneg hC0 hly)
    _ ≤ (max C 0 * (max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * X.la1 x ^ (-A))) * R := by gcongr
    _ = max C 0 * max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * R * X.la1 x ^ (-A) := by ring
end ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds
