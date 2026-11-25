-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.R_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:30.232253+00:00
-- url     : https://prove2.me/submissions/a21bbfaf-a518-4ed9-98d6-00af152133d8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_lact_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_lact_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_invF_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_assoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_invF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_oneF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (x0 : Frame X.Ψ r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
theorem _root_.solution {z z' : V (nd X)} (h : R X x0 z z') : R X x0 z' z := by
  obtain ⟨δ, hδ, b, hb, h⟩ := h
  refine ⟨δ⁻¹, X.Γ.inv_mem hδ, ExtFPf.invF X b, ExtFPf.invF_mem X hb, ?_⟩
  calc lact δ⁻¹ (cpt X x0 z') = lact δ⁻¹ (lact δ (rmul (cpt X x0 z) (ExtFPf.invF X b))) := by
        rw [lact_rmul, h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
    _ = _ := lact_inv _ _
end ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
