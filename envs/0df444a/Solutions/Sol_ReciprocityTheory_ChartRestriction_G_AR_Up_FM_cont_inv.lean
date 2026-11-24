-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FM.cont_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:53.380858+00:00
-- url     : https://prove2.me/submissions/f2041c8c-17b5-428c-826d-55bdbed81beb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfA

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
noncomputable section
attribute [local instance] Classical.propDecidable
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM
theorem _root_.solution {α : Type*} [TopologicalSpace α] {n : ℕ} {f : α → Matrix (Fin n) (Fin n) ℂ}
    (hf : Continuous f) (hd : ∀ a, (f a).det ≠ 0) : Continuous fun a => (f a)⁻¹ := by
  have h : (fun a => (f a)⁻¹) = fun a => (f a).det⁻¹ • (f a).adjugate := by
    funext a
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hf.matrix_det.inv₀ hd).smul hf.matrix_adjugate
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
