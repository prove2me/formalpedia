-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FM.not_dom_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:18.982002+00:00
-- url     : https://prove2.me/submissions/71e006f5-5895-4309-8da4-1b78be5f4de3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfC
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_invF_mem__0cc67cfea2e1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_UF_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_rmul_invF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthogonalFrameDomain_rmul_mem_dom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
attribute [local instance] haarF haarIx
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM
theorem _root_.solution {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {p : Frame X.Ψ r} (hp : p ∉ X.dom)
    {y : UpI X.Ψ r → ℂ} (hd : ∀ τ b, y (dI τ b) ≠ 0) : rmul p (UF X y) ∉ C := fun h => by
  have hb := UF_mem X hd
  have := OrthogonalFrameDomain.rmul_mem_dom X (hCd h) (invF_mem' X hb)
  rw [rmul_invF X hb] at this
  exact hp this
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
