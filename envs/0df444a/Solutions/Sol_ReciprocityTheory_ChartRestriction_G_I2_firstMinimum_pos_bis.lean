-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.firstMinimum_pos_bis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:07:25.753831+00:00
-- url     : https://prove2.me/submissions/d540bf96-10f0-4312-9bd4-9c68a2a5cda2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_card_idx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_PT_firstMinimum_toTorus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_firstMinimum_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) : 0 < X.la1 := by
  rw [← X.firstMinimum_toTorus]
  apply firstMinimum_pos
  rw [X.card_idx]
  have h := P.hfr
  unfold PT.gA
  omega
end ReciprocityTheory.ChartRestriction.G.I2
