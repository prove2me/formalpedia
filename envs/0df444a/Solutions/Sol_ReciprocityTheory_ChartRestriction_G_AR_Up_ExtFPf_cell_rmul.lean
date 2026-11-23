-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.cell_rmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:46.453797+00:00
-- url     : https://prove2.me/submissions/d9791158-78da-4bcf-a23c-20eafbef6443

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_assoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_mul_mem

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
theorem _root_.solution {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hΔ : D.Δ x ≠ 0) (hb : b ∈ Bor X.Ψ r) :
    D.Δ (rmul x b) ≠ 0 ∧ D.zOf (rmul x b) = D.zOf x ∧ D.bOf (rmul x b) = rmul (D.bOf x) b := by
  obtain ⟨hz, hbx, hxe⟩ := D.split x hx hΔ
  have e : rmul x b = rmul (cpt X x0 (D.zOf x)) (rmul (D.bOf x) b) := by
    rw [← rmul_assoc X, ← hxe]
  obtain ⟨h1, h2, h3⟩ := D.uniq (D.zOf x) hz (rmul (D.bOf x) b) (mul_mem X hbx hb)
  rw [e]
  exact ⟨h1, h2, h3⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
