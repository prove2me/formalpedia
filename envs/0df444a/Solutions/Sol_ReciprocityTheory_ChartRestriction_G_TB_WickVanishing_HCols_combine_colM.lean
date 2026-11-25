-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols.combine_colM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:58.749148+00:00
-- url     : https://prove2.me/submissions/a2b7e1e1-a492-42f8-a34f-bc2bf5b9c438

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSCCols
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaHCols
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_combine_apply
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
theorem _root_.solution (mo : ι × Fin n →₀ ℕ) : combine (colM mo) = mo := by
  ext ⟨l, b⟩
  rw [combine_apply]
  simp [colM]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
