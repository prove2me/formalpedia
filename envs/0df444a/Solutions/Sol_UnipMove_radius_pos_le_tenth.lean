-- Prove2me | solution 1 for UnipMove.radius_pos_le_tenth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:20.873832+00:00
-- url     : https://prove2.me/submissions/512382ef-a7b8-42e2-9a6c-7fb33295ede0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoNormRelationTamePrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace UnipMove
theorem _root_.solution : RadiusPosLeTenth := by
  intro c1 w hc1 hw
  unfold d6rh
  have hπ := Real.pi_gt_three
  have hpos : 0 < 12 * Real.pi * (c1 + w) := by positivity
  refine ⟨by positivity, one_div_le_one_div_of_le (by norm_num) ?_⟩
  nlinarith
end UnipMove
