-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols.Mf_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:57:27.556356+00:00
-- url     : https://prove2.me/submissions/ab7de32c-cb5e-40aa-9b00-a15d52b002bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSCCols
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaHCols
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_Mf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_Mf_zero
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
theorem _root_.solution {α : Type} (s : Finset α) (P : α → MvPolynomial (ι × Fin n) k) :
    Mf mu (∑ a ∈ s, P a) = ∑ a ∈ s, Mf mu (P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Mf_zero mu]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Mf_add, ih]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
