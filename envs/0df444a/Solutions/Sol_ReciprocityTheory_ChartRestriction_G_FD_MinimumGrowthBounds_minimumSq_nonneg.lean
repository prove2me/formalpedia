-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:54:41.649543+00:00
-- url     : https://prove2.me/submissions/7150cf3a-0fa8-4c7d-aa33-b364640b09ba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MinimumGrowthBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_maj_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TwoSidedBoostBounds_c_pos


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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) : 0 ≤ X.firstMinimumSq x := by
  apply Real.sInf_nonneg
  rintro t ⟨v, _, _, rfl⟩
  exact Finset.sum_nonneg fun τ _ =>
    mul_nonneg (TwoSidedBoostBounds.c_pos (X := X) τ).le (MajorantConjugateTransfer.maj_nonneg (X := X) hx τ _)
end ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds
