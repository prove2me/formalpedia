-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.cell_of_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:52.703798+00:00
-- url     : https://prove2.me/submissions/57e22677-be29-46c4-b271-2936b6341eb3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_oneF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_assoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_invF_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_invF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_cell_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthogonalFrameDomain_rmul_mem_dom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
theorem _root_.solution {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (hΔ : D.Δ (rmul x b) ≠ 0) : D.Δ x ≠ 0 := by
  have hxb : rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom (X := X) hx hb
  have h := (cell_rmul D hxb hΔ (invF_mem X hb)).1
  rwa [rmul_assoc X, rmul_invF X hb, rmul_oneF X] at h
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
