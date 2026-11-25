-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols.degree_colM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:12:16.787265+00:00
-- url     : https://prove2.me/submissions/05ce841c-d628-49e8-9792-9fdfec2de3fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSCCols
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaHCols
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}
variable (mu : Fin n → MvPolynomial ι k →ₗ[k] k)
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
theorem _root_.solution (mo : ι × Fin n →₀ ℕ) : ∑ b, (colM mo b).degree = mo.degree := by
  classical
  have hd : ∀ {σ : Type} [Fintype σ] (m : σ →₀ ℕ), m.degree = ∑ i, m i := by
    intro σ _ m
    unfold Finsupp.degree
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
  simp only [hd]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [colM]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
