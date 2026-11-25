-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FM.mem_sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:16.04065+00:00
-- url     : https://prove2.me/submissions/3101e722-94c7-4dd9-97a2-e771f363d6c3

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
theorem _root_.solution {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {x0 : Frame X.Ψ r} {z : V (nd X)}
    {y : UpI X.Ψ r → ℂ} (hd : ∀ τ b, y (dI τ b) ≠ 0) (hxC : rmul (cpt X x0 z) (UF X y) ∈ C) :
    z ∈ sat X x0 C := by
  have hb := UF_mem X hd
  refine ⟨?_, rmul (cpt X x0 z) (UF X y), hxC, invF X (UF X y), invF_mem' X hb, (rmul_invF X hb).symm⟩
  show cpt X x0 z ∈ X.dom
  have := OrthogonalFrameDomain.rmul_mem_dom X (hCd hxC) (invF_mem' X hb)
  rwa [rmul_invF X hb] at this
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
