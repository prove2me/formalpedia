-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI__0_upper_9db1d5f297f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:05:55.591016+00:00
-- url     : https://prove2.me/submissions/a450669c-2926-4e8e-9934-788d03932c43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_bOf_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bOf_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) : (β0 X y τ).BlockTriangular id := by
  have h := bOf_mem (X := X) hy
  simp only [Bor, Set.mem_setOf_eq] at h
  have hu : (mat (bOf X y) τ).BlockTriangular id := fun a c hac => (h τ).2 a c hac
  letI := (mat (bOf X y) τ).invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 (bOf_det X hy τ))
  exact Matrix.blockTriangular_inv_of_blockTriangular hu
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
