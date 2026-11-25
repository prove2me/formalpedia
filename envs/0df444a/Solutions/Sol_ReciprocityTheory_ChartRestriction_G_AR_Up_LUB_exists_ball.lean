-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUB.exists_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:43:41.306569+00:00
-- url     : https://prove2.me/submissions/240e4c72-c4bf-432f-bfad-231922ad0460

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUB_cell_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_isOpen_OmF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_continuous_cpt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
theorem _root_.solution (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) :
    ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∀ z ∈ Metric.ball (0 : V (nd X)) ρ1, cpt X (rmul x1' b1) z ∈ ExtFPf.cell D := by
  have hopen : IsOpen {z : V (nd X) | cpt X (rmul x1' b1) z ∈ ExtFPf.cell D} := by
    have h1 := ExF.isOpen_OmF (X := X) (rmul x1' b1)
    have h2 : IsOpen {z : V (nd X) | D.Δ (cpt X (rmul x1' b1) z) ≠ 0} :=
      isOpen_ne_fun (D.hΔ.continuous.comp (MI.continuous_cpt (X := X) _)) continuous_const
    exact h1.inter h2
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen 0 (cell_zero X b1 D ho' hb1)
  exact ⟨ρ, hρ, fun z hz => hball hz⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
