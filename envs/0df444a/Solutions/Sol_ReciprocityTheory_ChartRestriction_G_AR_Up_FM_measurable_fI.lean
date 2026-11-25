-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FM.measurable_fI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:49.180818+00:00
-- url     : https://prove2.me/submissions/62b62955-a690-437e-b8f9-db0dbdefd705

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_continuous_UF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_continuous_rmul

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
theorem _root_.solution {C : Set (Frame X.Ψ r)} (hCm : MeasurableSet C) : Measurable (fI X C) := by
  have hJ : Continuous (fun y : UpI X.Ψ r → ℂ => jacU y) := by
    unfold jacU
    apply continuous_finset_prod
    intro i _
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  have hS : MeasurableSet {q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) | ∀ τ b, q.2 (dI τ b) ≠ 0} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun τ => MeasurableSet.iInter fun b => ?_
    have hc : Continuous fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) => q.2 (dI τ b) :=
      (continuous_apply (dI τ b) : Continuous fun y : UpI X.Ψ r → ℂ => y (dI τ b)).comp continuous_snd
    exact (isOpen_ne_fun hc continuous_const).measurableSet
  have hf : Measurable (fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) =>
      ENNReal.ofReal (Complex.normSq (jacU q.2))) :=
    ENNReal.measurable_ofReal.comp ((Complex.continuous_normSq.comp (hJ.comp continuous_snd)).measurable)
  have hg : Measurable (fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) =>
      C.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul q.1 (UF X q.2))) :=
    (measurable_one.indicator hCm).comp
      ((continuous_rmul X).comp (continuous_fst.prodMk ((continuous_UF X).comp continuous_snd))).measurable
  unfold fI
  exact Measurable.ite hS (hf.mul hg) measurable_const
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
