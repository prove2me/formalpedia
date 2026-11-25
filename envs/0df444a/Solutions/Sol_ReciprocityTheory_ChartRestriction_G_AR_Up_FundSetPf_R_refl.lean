-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.R_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:26.926064+00:00
-- url     : https://prove2.me/submissions/7f02ec91-4817-4d07-aa7c-37c1760e711f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_lact_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_oneF_mem
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
theorem _root_.solution (z : V (nd X)) : R X x0 z z :=
  ⟨1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, by rw [lact_one, ExtFPf.rmul_oneF]⟩
end ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
