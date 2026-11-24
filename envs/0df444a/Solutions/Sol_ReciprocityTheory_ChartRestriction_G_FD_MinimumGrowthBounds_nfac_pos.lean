-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.nfac_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:32.449334+00:00
-- url     : https://prove2.me/submissions/b1f4e52f-f21e-49bd-a8b7-468b1ee4475c

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
theorem _root_.solution (la : Wt X.Ψ r) {y : Frame X.Ψ r} (hy : y ∈ X.dom) : 0 < X.nfac la y := by
  have hd : ∀ τ i, dmin X.Gm y τ i ≠ 0 := by
    intro τ i h0
    have h1 := (hy τ).2 i
    rw [h0] at h1
    simp at h1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _
end ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds
