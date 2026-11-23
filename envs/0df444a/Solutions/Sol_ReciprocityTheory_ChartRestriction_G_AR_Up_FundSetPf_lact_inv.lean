-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:14.066093+00:00
-- url     : https://prove2.me/submissions/7f39b9ae-08eb-4176-9598-f0e6b13718c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_lact_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_lact_one

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
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) (y : Frame Ψ r) : lact δ⁻¹ (lact δ y) = y := by
  rw [← lact_mul, inv_mul_cancel, lact_one]
end ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
