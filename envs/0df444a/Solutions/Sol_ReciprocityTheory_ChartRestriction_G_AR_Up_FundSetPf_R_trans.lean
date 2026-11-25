-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.R_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:34.338605+00:00
-- url     : https://prove2.me/submissions/1f7c7934-475a-4db9-bea4-ede8a16bf684

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_lact_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_lact_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_mul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_assoc


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
theorem _root_.solution {z z' z'' : V (nd X)} (h1 : R X x0 z z') (h2 : R X x0 z' z'') : R X x0 z z'' := by
  obtain ⟨δ1, hδ1, b1, hb1, h1⟩ := h1
  obtain ⟨δ2, hδ2, b2, hb2, h2⟩ := h2
  exact ⟨δ2 * δ1, X.Γ.mul_mem hδ2 hδ1, rmul b2 b1, ExtFPf.mul_mem X hb2 hb1, by
    rw [lact_mul, h1, lact_rmul, h2, ExtFPf.rmul_assoc]⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
