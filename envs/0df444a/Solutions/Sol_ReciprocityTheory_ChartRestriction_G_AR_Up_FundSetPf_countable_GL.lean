-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.countable_GL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:55:58.441114+00:00
-- url     : https://prove2.me/submissions/10c03f0c-8a7d-422c-99c5-dc5f5b2023a1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf

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
theorem _root_.solution : Countable (GL (Fin r) E) := by
  have : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  have : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact Function.Injective.countable fun a b h => Units.ext h
end ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
