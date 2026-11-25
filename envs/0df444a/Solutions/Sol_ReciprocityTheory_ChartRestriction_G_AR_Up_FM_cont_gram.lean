-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FM.cont_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:29.353726+00:00
-- url     : https://prove2.me/submissions/db24db2f-b6c2-4f2e-8d32-2a8ecfe1d42a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_cont_mat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private theorem continuous_gram_comp {α : Type*} [TopologicalSpace α] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {f : α → Matrix (Fin r) (Fin r) ℂ} (hf : Continuous f) :
    Continuous fun a => ReciprocityTheory.ChartRestriction.G.FD.gram τ G (f a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact (((continuous_apply i).comp ((continuous_apply a).comp hf)).mul continuous_const).mul
    (Complex.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply b).comp hf)))
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM
theorem _root_.solution (τ : X.Ψ) : Continuous fun y : Frame X.Ψ r => gram τ.1 X.Gm (mat y τ) := by
  exact continuous_gram_comp τ.1 X.Gm (cont_mat X τ)
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
